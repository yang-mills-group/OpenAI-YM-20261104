import YM.WilsonCoeffUV.Series.VectorJac
/-! Held and evaluated extra time for the homotopy. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Matrix Function PowerSeries
open scoped BigOperators
variable {U Y Z : Type*}

section hom
lemma hold_real (a : ℝ) : holdUp U (realS (U:=Y) a) = realS a := by
  rw [show realS a=C (MvPolynomial.C a) from rfl, holdUp, map_C]; simp [holdUpPoly]
lemma hold_X' : holdUp U (X:Ink Y)=X := by simp [holdUp]
variable (U Y)
def see (c:ℝ) : Ink (Option Y) →+* Ink Y:= PowerSeries.map (stopT c).toRingHom
def hide : Ink Y →+* Ink (Option Y):= PowerSeries.map (launchT (U:=Y)).toRingHom
variable {U Y}
lemma arrive (p:Ink Y)(c) : see Y c (hide Y p)=p := by ext1 n; simp only [see,hide,coeff_map]; apply stopT_launch
lemma see_ext {p:Ink (Option Y)} (h:brush none p=0)(c d : ℝ) : see Y c p = see Y d p := by
  ext1 n; have he:=congrArg (coeff n) h; simp only [brush,blot_apply,map_zero] at he; simp only [see,coeff_map]; apply time_only he
lemma see_X (c:ℝ) : see Y c X=X := by simp [see]
lemma see_real (c a:ℝ): see Y c (realS a)=realS a := by rw [see,show realS a=C (MvPolynomial.C a) from rfl, map_C]; simp [stopT,MvPolynomial.algebraMap_eq]
lemma latent (p:Ink Y) : brush none (hide Y p)=0 := by
  have h (q:POL Y) : MvPolynomial.pderiv none (launchT q)=0 := by
    apply (MvPolynomial.optionEquivLeft ℝ Y).injective; rw [← tick,toc, launched, Polynomial.derivative_C,map_zero]
  ext1 n; simp only [brush,blot_apply, hide,coeff_map,map_zero]; exact h _

def hideF (U Y : Type*) : Ink (U⊕Y) →+* Ink (U⊕Option Y) := PowerSeries.map (MvPolynomial.rename (Sum.map id some)).toRingHom
end hom

section
variable [Fintype U][DecidableEq U]
lemma unit_pin (i:U) : noiseLine (Y:=Y) (1:Matrix U U ℝ) i= path (.inl i) := by
  rw [noiseLine,Finset.sum_eq_single i]
  · simp
  · intro b _ h; rw [one_apply_ne h.symm,zero_smul]
  simp

def watch (U Y : Type*) [Fintype U][DecidableEq U](c:ℝ) : Ink (U⊕Option Y) →+* Ink (U⊕Y):= railCov 1 (fun i=> see Y c (path i))
lemma watch_pin (i:U)(x:ℝ): watch U Y x (path (.inl i)) = path (.inl i) := by rw [watch,rail_pin,unit_pin]
lemma watch_X (x): watch U Y x X=X := by rw [watch,railCov,train_X]
lemma watch_real (x c): watch U Y x (realS c)=realS c := rail_zero ..

lemma watch_comp (W:Y→ Ink (Option Z))(θ:U→ Ink (U⊕Option Z)) (x:ℝ) :
    (watch U Z x).comp (reroll W θ)=reroll (fun i=>see Z x (W i)) (fun i=>watch U Z x (θ i)) := by
  have hup : (watch U Z x).comp (holdUp U)=(holdUp U).comp (see Z x) := by
    let p:= (watch U Z x).comp (holdUp U)
    let q:=(holdUp U).comp (see Z x);
    have hx : p X=X := by change watch U Z x _=X; rw [hold_X',watch_X]
    have hX : q X=X := by change holdUp U _=X; rw [see_X,hold_X']
    change p=q; apply serial_ext (by rw [hx]; simp) _ (hx.trans hX.symm); intro u
    induction u using MvPolynomial.induction_on with
    | C a =>
      change watch U Z x (holdUp _ (realS a))= holdUp _ (see Z x (realS a)); rw [hold_real,watch_real,see_real,hold_real]
    | add u v a b=> simp_rw [map_add,a,b]
    | mul_X u i h=> simp only [map_mul,h,show C _=path i from rfl]; refine congrArg (q (C u) * ·) (show p (path i)=q (path i) from ?_)
                    change watch U Z x (holdUp U (path i))= _; rw [up_var, watch, rail_aux]; rfl
  let p:= (watch U Z x).comp (reroll W θ); let q:=reroll (fun i=>see Z x (W i)) (fun i=>watch U Z x (θ i))
  have hx : p X=X:= by change watch U Z x _= _; rw [reroll,train_X,watch_X];
  change p=q; apply serial_ext (by rw [hx]; simp) _ (hx.trans (train_X _).symm)
  intro u; induction u using MvPolynomial.induction_on with
  | C a=> change watch U Z x (train _ (realS a))=train _ (realS a); rw [train_real,train_real,watch_real]
  | add u v a b=> simp_rw [map_add,a,b]
  | mul_X u i h=> simp only [map_mul,h,show C _=path i from rfl]; refine congrArg (q (C u) * ·) (show p (path i)=q (path i) from ?_)
                  change watch U Z x (train (Sum.elim _ _) (path i))= train (Sum.elim _ _) (path i); rw [train_path,train_path]; cases i with
                  | inl i=> rfl
                  | inr i=> exact DFunLike.congr_fun hup (W i)
lemma watch_jac [Fintype Y](θ:U→Ink (U⊕Option Y))(x): watch U Y x (motionJ θ).det=(motionJ fun i=>watch U Y x (θ i)).det := by
  rw [RingHom.map_det]; congr 1; ext1 i j
  change watch U Y x (brush (.inl j) _)=brush (.inl j) _
  rw [watch,rail_dir]; rw [Finset.sum_eq_single j];
  · rw [one_apply_eq,one_smul]
  · intro a _ e; rw [one_apply_ne e,zero_smul]
  simp
lemma watch_wick [Fintype Y]{H:Matrix U U ℝ}(hh:H.transpose=H)(p: Ink (U⊕Option Y))(x:ℝ): Wick Y H (watch U Y x p)=see Y x (Wick (Option Y) H p) := by
  rw [watch,W_linear _ _ hh hh (by simp)]
  exact congrArg (fun f: Ink (Option Y) →+* Ink Y=> f _) (rail (see_X _) (fun i=>see_real x i)).symm
lemma revisit (p:Ink (U⊕Y))(x:ℝ) : watch U Y x (hideF U Y p)=p := by
  suffices H : (watch U Y x).comp (hideF U Y)=RingHom.id _ by exact DFunLike.congr_fun H _
  apply serial_ext (by simp only [hideF,RingHom.comp_apply,map_X,watch_X,constantCoeff_X]) _ (by simp [hideF,watch_X]); intro w
  induction w using MvPolynomial.induction_on with
  | C a=>
    have h: hideF U Y (C (MvPolynomial.C a)) = realS a := by simp [hideF,realS]
    rw [RingHom.comp_apply,h,watch_real]; rfl
  | add w v a b=> simp_rw [map_add,a,b]
  | mul_X u i h=> simp only [map_mul,h,show C _=path i from rfl]; congr 1
                  have he : hideF U Y (path i)=path (Sum.map id some i) := by rw [hideF,path,map_C]; simp [path]
                  change watch U Y x _= _; rw [he]; cases i with
                  | inl i=> exact watch_pin _ _
                  | inr i=>
                    rw [Sum.map_inr,watch,rail_aux]
                    have hh : see Y x (path (some i))=path i:= by rw [see,path,map_C]; simp [stopT,path]
                    rw [hh,up_var]; rfl
lemma watch_time (c:ℝ): watch U Y c (path (.inr none))= realS c := by
  rw [watch,rail_aux]
  have he : see Y c (path none)=realS c := by rw [see,path,map_C]; simp [stopT,realS]
  rw [he,hold_real]
lemma watch_line (K:Matrix U U ℝ)(u:U)(x): watch U Y x (noiseLine K u)=noiseLine K u := by
  have h (c:ℝ)(p): watch U Y x (c•p)=c • watch U Y x p := train_smul ..
  unfold noiseLine; simp_rw [map_sum,h,watch_pin]
lemma watch_score (K:Matrix U U ℝ)(x): watch U Y x (bodyQ (Option Y) K)= bodyQ Y K := by
  have h (c:ℝ)(p): watch U Y x (c•p)=c • watch U Y x p := train_smul ..
  simp_rw [bodyQ,slopeQ,h,map_sum,map_mul,map_sum,h,watch_pin]
end
end YM.WilsonCoeffUV.Blue
