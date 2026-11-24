import YM.WilsonCoeffUV.Series.Caloric
import Mathlib.Data.Matrix.Block

/-! X-adic Wick reader with smooth log parameter slots, including linear
noise map to or from padded singular covariances. Proven solely in the
independent algebra. Real moments are not hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Matrix Function PowerSeries
open scoped Classical BigOperators
variable {U V X' Y Y' : Type*}

section
variable [Fintype U]
abbrev blur (G:Matrix U U ℝ) := overlay (glaze G)
omit [Fintype U] in
lemma overlay_Xpow (d:POL U→ₗ[ℝ]POL V)(f:Ink U)(i:ℕ) : overlay d (f*X^i)=overlay d f*X^i := by
  ext1 n; simp only [overlay_apply,coeff_mul_X_pow']; split<;>simp
lemma blur_deriv (G:Matrix U U ℝ)(p:Ink U)(i:U) : blur G (brush i p)= brush i (blur G p) := by
  ext1 n; rw [overlay_apply,brush,blot_apply, glaze_deriv,blot_apply,overlay_apply]
omit [Fintype U] in
lemma overlayEq {f g:Ink U}{k}(h:Equal k f g)(d:POL U→ₗ[ℝ]POL V) : Equal k (overlay d f) (overlay d g) := by intro i hi; simp only [overlay_apply,h i hi]
omit [Fintype U] in
lemma overlay_C (d:POL U→ₗ[ℝ]POL V)(v:POL U) : overlay d (C v)=C (d v) := by
  ext1 n; simp only [overlay_apply,coeff_C]; split<;>simp
lemma blur_one (G:Matrix U U ℝ): blur G 1=1 := by rw [show (1:Ink U)= C (1:POL U) from (map_one C).symm, overlay_C, glaze_one]
lemma blur_var (G:Matrix U U ℝ) (p:Ink U)(i:U) : blur G (p * path i)= blur G p * path i + ∑ j:U, blend G i j • brush j (blur G p) := by
  ext1 n; rw [overlay_apply]; simp only [path,coeff_mul_C,map_add,map_sum, coeff_smul,brush,blot_apply, overlay_apply,glaze_pin,glaze_deriv]
end

/-- Block diagonal with auxiliary external colours -/
def fillSlots (Y:Type*)(G:Matrix U U ℝ) : Matrix (U⊕Y) (U⊕Y) ℝ:= fromBlocks G 0 0 0

def projectZeroPoly (U Y:Type*): POL (U⊕Y) →ₐ[ℝ] POL Y := MvPolynomial.aeval (Sum.elim 0 MvPolynomial.X)
def projectZero : Ink (U⊕Y)→+*Ink Y := PowerSeries.map (projectZeroPoly U Y).toRingHom
def holdUpPoly (U Y:Type*): POL Y →ₐ[ℝ] POL (U⊕Y):= MvPolynomial.rename Sum.inr
def holdUp (U:Type*) {Y:Type*} : Ink Y→+* Ink (U⊕Y):= PowerSeries.map (holdUpPoly U Y).toRingHom
lemma project_var (p:U) : projectZero (path (Sum.inl (β:=Y) p)) =0 := by rw [projectZero,path,map_C]; simp [projectZeroPoly]
lemma project_ext (i:Y): projectZero (path (Sum.inr (α:=U) i))=path i := by rw [projectZero,path,map_C]; simp [projectZeroPoly,path]
lemma up_var (i:Y): holdUp U (path i) = path (Sum.inr i) := by rw [holdUp,path,map_C]; simp [holdUpPoly,path]
lemma project_up (f:Ink Y) : projectZero (holdUp U f) = f := by
  have h i : projectZeroPoly U Y (holdUpPoly U Y i)=i := by
    induction i using MvPolynomial.induction_on with
    | C a=> simp [projectZeroPoly,holdUpPoly,MvPolynomial.algebraMap_eq]
    | add p q a b=> rw [map_add,map_add,a,b]
    | mul_X p j h=> simp only [map_mul,h]; congr 1; simp [projectZeroPoly,holdUpPoly]
  ext1 n; simp only [projectZero,holdUp,coeff_map]; exact h _
lemma project_drop (f:Ink (U⊕Y))(y:Y): projectZero (brush (.inr y) f)= brush y (projectZero f) := by
  have h w : projectZeroPoly U Y (MvPolynomial.pderiv (.inr y) w)=MvPolynomial.pderiv y (projectZeroPoly U Y w):= by
    induction w using MvPolynomial.induction_on with
    | C a=> simp [projectZeroPoly]
    | add p q a b => simp_rw [map_add,a,b]
    | mul_X p j h=> rw [MvPolynomial.pderiv_mul,map_add,map_mul,map_mul,map_mul,MvPolynomial.pderiv_mul,h]; cases j <;> simp [projectZeroPoly, Pi.single_apply,apply_ite]; split_ifs <;> simp_all
  ext1 n; simp only [projectZero,brush, coeff_map,blot_apply]; exact h _
lemma up_vacant (i:U)(f:Ink Y) : brush (.inl i) (holdUp U f)=0 := by
  have h w : MvPolynomial.pderiv (.inl i) (holdUpPoly U Y w)=0 := by
    induction w using MvPolynomial.induction_on with
    | C a=> simp [holdUpPoly]
    | add p q a b=> rw [map_add,map_add,a,b,zero_add]
    | mul_X p j h=> rw [map_mul,MvPolynomial.pderiv_mul,h]; simp [holdUpPoly]
  ext1 n; simp only [brush, holdUp, blot_apply, coeff_map,map_zero]; exact h _
lemma project_smul (c:ℝ)(f:Ink (U⊕Y)): projectZero (c•f)=c•projectZero f := by
  ext1 n; simp only [projectZero,coeff_map,coeff_smul]; apply map_smul (projectZeroPoly U Y)

-- linear covariance intertwiner
section
variable [Fintype U][Fintype Y]
abbrev fullB (Y:Type*)[Fintype Y](G:Matrix U U ℝ) := blur (fillSlots Y G)
lemma full_noise (G:Matrix U U ℝ)(p:Ink (U⊕Y))(a:U) : fullB Y G (p*path (.inl a))=fullB Y G p*path (.inl a)+ ∑ b:U,blend G a b • brush (.inl b) (fullB Y G p) := by
  rw [blur_var,Fintype.sum_sum_type]; simp [blend,fullB,fillSlots]
lemma full_const (G:Matrix U U ℝ) (p:Ink (U⊕Y)) (v:Y): fullB Y G (p*path (.inr v))=fullB Y G p*path (.inr v) := by
  rw [blur_var,Fintype.sum_sum_type]; simp [blend,fullB,fillSlots]
lemma full_auxiliary (G:Matrix U U ℝ)(p:Ink (U⊕Y))(f:Ink Y) : fullB Y G (p * holdUp U f) = fullB Y G p * holdUp U f := by
  have he w : fullB Y G (p * holdUp U (C w))=fullB Y G p*holdUp U (C w) := by
    induction w using MvPolynomial.induction_on with
    | C a=>
      rw [holdUp,map_C]; simp only [holdUpPoly]
      erw [MvPolynomial.rename_C];
      rw [show C (MvPolynomial.C a) = algebraMap ℝ _ a from (real_alg a).symm,mul_comm,mul_comm (fullB Y G p),←Algebra.smul_def,←Algebra.smul_def,map_smul]
    | add f g hf hg=> simp only [map_add,mul_add,hf,hg]
    | mul_X f a h=> rw [map_mul C,map_mul (holdUp U),show C (MvPolynomial.X a)=path a from rfl,up_var,← mul_assoc,full_const G, h, mul_assoc];
  ext1 n; let g:= fillSlots Y G
  have h := filtered (ξ:=holdUp U (Y:=Y)) (by simp [holdUp]) (shave f (n+1))
  rw [overlayEq ((Equal.refl p _).mul h) (glaze g) n n.lt_succ_self, ((Equal.refl (fullB Y G p) _).mul h) n n.lt_succ_self]
  simp_rw [map_sum, Finset.mul_sum,map_mul (holdUp U),map_pow, show holdUp U (X:Ink Y)=X by simp [holdUp],←mul_assoc]
  -- use he
  simp_rw [←he,map_sum,overlay_Xpow]; rfl

abbrev Wick (Y:Type*) [Fintype Y](G:Matrix U U ℝ) : Ink (U⊕Y)→Ink Y := fun f=> projectZero (fullB Y G f)
lemma W_add (G:Matrix U U ℝ)(p q:Ink (U⊕Y)) : Wick Y G (p+q)=Wick Y G p+Wick Y G q := by simp only [Wick,map_add]
lemma W_sum (G:Matrix U U ℝ){I :Type*}(s:Finset I)(p:I→Ink (U⊕Y)): Wick Y G (∑ i∈s,p i)=∑ i∈s,Wick Y G (p i) := by simp only [Wick,map_sum]
lemma W_smul (G:Matrix U U ℝ)(p:Ink (U⊕Y))(r:ℝ) : Wick Y G (r•p)=r • Wick Y G p := by simp only [Wick,map_smul,project_smul]
lemma W_one (G:Matrix U U ℝ) : Wick Y G 1=1 := by rw [Wick,blur_one,map_one]
lemma W_param (G:Matrix U U ℝ)(p:Ink (U⊕Y))(f:Ink Y): Wick Y G (p*holdUp U f)=Wick Y G p*f := by rw [Wick,full_auxiliary,map_mul,project_up]
lemma W_var (G:Matrix U U ℝ)(h:G.transpose=G)(p:Ink (U⊕Y))(a:U): Wick Y G (p * path (.inl a))=∑ b:U,G a b • Wick Y G (brush (.inl b) p) := by
  rw [Wick,full_noise, map_add,map_mul,project_var,mul_zero,zero_add,map_sum]
  have he b : blend G a b=G a b := by rw [blend,show G b a=G a b from congr_fun (congr_arg (fun M:Matrix U U ℝ=>M a) h) b]; ring
  exact Finset.sum_congr rfl (fun i _=> by rw [he,← blur_deriv,project_smul])
lemma W_D (G:Matrix U U ℝ)(p:Ink (U⊕Y))(y:Y) : Wick Y G (brush (.inr y) p)=brush y (Wick Y G p) := by rw [Wick,blur_deriv,project_drop]

end
section
variable [Fintype V]
def noiseLine (R:Matrix U V ℝ)(i:U) : Ink (V⊕Y) := ∑ v,R i v • path (.inl v)
lemma noiseLine_slope (R:Matrix U V ℝ)(i v) : brush (Sum.inl (β:=Y) v) (noiseLine R i)= realS (R i v) := by
  simp_rw [noiseLine,map_sum,Derivation.map_smul]
  rw [Finset.sum_eq_single v];
  · rw [brush_path]; simp only [reduceIte, ↓reduceIte,Algebra.smul_def,mul_one,real_alg]
  · intro w _ hh; rw [brush_path,if_neg (by simpa)]; simp
  simp

def railCov (R:Matrix U V ℝ)(W:Y→Ink Y'): Ink (U⊕Y)→+*Ink (V⊕Y') := train (Sum.elim (noiseLine R) (holdUp _ ∘ W))
lemma rail_pin (R:Matrix U V ℝ)(W:Y→Ink Y')(a:U): railCov R W (path (.inl a))=noiseLine R a := by rw [railCov,train_path]; rfl
lemma rail_aux (R:Matrix U V ℝ)(W:Y→Ink Y')(i:Y): railCov R W (path (.inr i))=holdUp V (W i) := by rw [railCov,train_path]; rfl
lemma rail_zero (R:Matrix U V ℝ)(W:Y→Ink Y')(i:ℝ): railCov R W (realS i) = realS i := by rw [railCov,train_real]
variable [Fintype U] [Fintype Y] [Fintype Y']
omit [Fintype Y'] in
lemma rail_dir (R:Matrix U V ℝ)(W:Y→Ink Y')(p:Ink (U⊕Y))(a:V) : brush (.inl a) (railCov R W p)=∑ i:U,R i a • railCov R W (brush (.inl i) p) := by
  rw [railCov, reroutes,Fintype.sum_sum_type]
  simp only [Sum.elim_inr, Function.comp_apply, up_vacant,zero_mul, Finset.sum_const_zero,add_zero, Sum.elim_inl,noiseLine_slope,Algebra.smul_def,real_alg]
private lemma railLine (R:Matrix U V ℝ)(W:Y→Ink Y'){G:Matrix U U ℝ}{H:Matrix V V ℝ}(hg:G.transpose=G)(hh:H.transpose=H)(e:G=R*H*R.transpose)(p:Ink (U⊕Y))(a:U)
    (hv:fullB Y' H (railCov R W p)=railCov R W (fullB Y G p)) :
    fullB Y' H (railCov R W (p*path (.inl a)))=railCov R W (fullB Y G (p*path (.inl a))) := by
  have e₁ i j : blend G i j=G i j := by rw [blend,show G j i=G i j from congr_fun (congr_arg (fun M:Matrix U U ℝ=>M i) hg) j]; ring
  have e₂ i j : blend H i j=H i j := by rw [blend,show H j i=H i j from congr_fun (congr_arg (fun M:Matrix V V ℝ=>M i) hh) j]; ring
  rw [map_mul,rail_pin,full_noise, map_add,map_mul (railCov R W),rail_pin]; simp_rw [noiseLine,Finset.mul_sum,map_sum,mul_smul_comm, map_smul (fullB Y' H), full_noise,hv,e₁,e₂, smul_add,Finset.sum_add_distrib]
  congr 1
  simp_rw [rail_dir,Finset.smul_sum]
  rw [Finset.sum_comm];
  simp_rw [railCov,train_smul,e, Matrix.mul_apply,Finset.sum_mul,Finset.sum_smul, Matrix.transpose_apply,smul_smul]
  -- reorder
  conv_lhs => enter [2,u]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]; simp only [mul_assoc]
set_option maxHeartbeats 600000 in
omit [Fintype Y] [Fintype Y'] [Fintype U] in
lemma rail_uncol (R:Matrix U V ℝ)(W:Y→Ink Y') : projectZero.comp (railCov R W)= (train W).comp projectZero := by
  apply serial_ext (by simp [projectZero,railCov]) _ (by simp [projectZero,railCov]); intro p
  have h j : projectZero (noiseLine (Y:=Y') R j)=0 := by simp_rw [noiseLine,map_sum,project_smul,project_var, smul_zero, Finset.sum_const_zero]
  induction p using MvPolynomial.induction_on with
  | C a=>
    have he (i): projectZero (realS (U:=V⊕Y') i)=realS i:=by simp [projectZero,projectZeroPoly,realS,MvPolynomial.algebraMap_eq]
    have hψ (i): projectZero (realS (U:=U⊕Y) i)=realS i:=by simp [projectZero,projectZeroPoly,realS,MvPolynomial.algebraMap_eq]
    change projectZero (railCov R W (realS a))= train W (projectZero (realS a))
    rw [rail_zero,he,hψ,train_real]
  | add f g a b=> simp_rw [map_add,a,b]
  | mul_X p j u=> simp only [map_mul,u]; congr 1; rw [show C _=path j from rfl,RingHom.comp_apply,RingHom.comp_apply]; cases j with
                    | inl i=> rw [rail_pin,project_var,map_zero,h]
                    | inr i=> rw [rail_aux,project_ext,train_path]; exact project_up _
lemma rail_blur (R:Matrix U V ℝ)(W:Y→Ink Y'){G:Matrix U U ℝ}{H:Matrix V V ℝ}(hg:G.transpose=G)(hh:H.transpose=H)(e:G=R*H*R.transpose)
    (p:Ink (U⊕Y)) : fullB Y' H (railCov R W p)=railCov R W (fullB Y G p) := by
  let ξ:=railCov R W
  have hx : ξ X=X := train_X _
  have he (v): fullB Y' H (ξ (C v))=ξ (fullB Y G (C v)) := by
    induction v using MvPolynomial.induction_on with
    | C a=>
      have hπ (u): ξ (realS u)=realS u:=rail_zero ..
      have he : fullB Y G (realS a)=realS a:=by rw [RingHom.comp_apply,overlay_C,glaze_constant]
      have hF : fullB Y' H (realS a)=realS a:=by rw [RingHom.comp_apply,overlay_C,glaze_constant]
      rw [show C _=realS a from rfl,hπ,he,hπ,hF]
    | add p q a b=> simp_rw [map_add,a,b]
    | mul_X p j h=> rw [map_mul C,show C (MvPolynomial.X j)=path j from rfl]; cases j with
                    | inl i=> exact railLine R W hg hh e _ _ h
                    | inr i=>
                      have he: ξ (path (.inr i))=holdUp V (W i):= rail_aux R W i
                      rw [full_const,map_mul ξ,map_mul ξ,he, full_auxiliary,h]
  have hv v k : fullB Y' H (ξ (C v*X^k))=ξ (fullB Y G (C v*X^k)) := by
    rw [map_mul ξ,map_pow,hx,overlay_Xpow, show fullB Y G (C v*X^k)=fullB Y G (C v)*X^k from overlay_Xpow ..]; change fullB Y' H _ * _= _; rw [he,map_mul,map_pow,hx]
  apply PowerSeries.ext; intro n
  have h := shave p (n+1)
  have h₁ := filtered (ξ:=ξ) (by rw [hx]; simp) h
  have h₂ := filtered (ξ:=ξ) (by rw [hx]; simp) (overlayEq h (glaze (fillSlots Y G)))
  refine (overlayEq h₁ (glaze (fillSlots Y' H)) n n.lt_succ_self).trans (Eq.trans ?_ (h₂ n n.lt_succ_self).symm)
  change coeff n (fullB Y' H (ξ _))=coeff n (ξ (fullB Y G _))
  simp_rw [map_sum,hv]
lemma W_linear (R:Matrix U V ℝ)(W:Y→Ink Y'){G:Matrix U U ℝ}{H:Matrix V V ℝ}(hg:G.transpose=G)(hh:H.transpose=H)(e:G=R*H*R.transpose)
    (p:Ink (U⊕Y)) : Wick Y' H (railCov R W p)=train W (Wick Y G p) := by
  rw [Wick,rail_blur _ _ hg hh e]; exact DFunLike.congr_fun (rail_uncol R W) _
end
end YM.WilsonCoeffUV.Blue
