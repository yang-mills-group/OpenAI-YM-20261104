import YM.WilsonCoeffUV.Series.TimeHomotopy
/-!
# Formal change of variables for W

Leading *noise* linear nonsingular is enough, no implicit uniform estimate.
Statements in real polynomial algebra before path tags. Gives self-symmetries
later even if geometric transformation doesn't fix the chosen block tree.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Matrix Function PowerSeries
open scoped BigOperators
variable {U Y Z : Type*} [Fintype U][DecidableEq U]

omit [Fintype U] [DecidableEq U] in
private lemma cc_train {u v:U→ Ink Y}(h:∀ i,constantCoeff (u i)=constantCoeff (v i))(f): constantCoeff (train u f) = constantCoeff (train v f) := by
  let α:= Finset.range (0+1)
  have hT (x : U→Ink Y) : constantCoeff (train x f)=constantCoeff (train x (C (constantCoeff f))) := by
    have he : Equal 1 f (C (constantCoeff f)) := by intro i hi; rw [show i=0 by omega]; simp
    simpa only [coeff_zero_eq_constantCoeff_apply] using (filtered (ξ:=train x) (by simp) he 0 (by simp))
  have ht p: constantCoeff (train u (C p))=constantCoeff (train v (C p)) := by
    induction p using MvPolynomial.induction_on with
    | C a=> simp only [show C _=realS a from rfl,train_real]
    | add p q a b=> simp only [map_add,a,b]
    | mul_X p i a=> simp only [map_mul,a,show C _=path i from rfl,train_path,h i]
  rw [hT u,hT v]; apply ht
lemma jac_lead {A:Matrix U U ℝ} (Y:Type*) : (motionJ (noiseLine (Y:=Y) A)).det = realS A.det := by
  rw [RingHom.map_det]; congr 1; ext1 i j; exact noiseLine_slope ..
omit [DecidableEq U] in
lemma local_zero_roll {K N:Matrix U U ℝ}(R:Matrix U U ℝ){θ:U→ Ink (U⊕Z)} (W:Y→Ink Z)
   (h:∀ i,constantCoeff (θ i)=constantCoeff (noiseLine R i))(hk:K=R.transpose*N*R) :
    constantCoeff (bodyQ Z K-reroll W θ (bodyQ Y N))=0 := by
  rw [map_sub,← form_rotate W R hk,reroll, railCov]
  apply sub_eq_zero.mpr
  apply cc_train; intro i; cases i; exact (h _).symm; rfl
private lemma jac_unit {A:Matrix U U ℝ}(hp:IsUnit A.det){θ:U→ Ink (U⊕Z)}(h:∀ i,constantCoeff (θ i)=constantCoeff (noiseLine A i)) : IsUnit (motionJ θ).det := by
  have hx : constantCoeff (motionJ θ).det=constantCoeff (motionJ (noiseLine (Y:=Z) A)).det := by
    simp_rw [RingHom.map_det]; apply congrArg det; ext1 i j
    have hg (f:Ink (U⊕Z)) : constantCoeff (brush (.inl j) f)=MvPolynomial.pderiv (.inl j) (constantCoeff f):= by rw [←coeff_zero_eq_constantCoeff_apply,←coeff_zero_eq_constantCoeff_apply,brush,blot_apply]
    exact (hg (θ i)).trans ((congrArg _ (h i)).trans (hg _).symm)
  rw [PowerSeries.isUnit_iff_constantCoeff,hx,jac_lead]
  exact (hp.map realS).map constantCoeff

/-- Formal Jacobian change for a motion of internal variables over arbitrary
external only spectators. Interpret exp solely X-adically. The conditions imply
`local_zero_roll`, required before Exp. Determinant of the leading linear map
(not its absolute value) occurs on the right. -/
theorem W_covariance [Fintype Z][Fintype Y]{H K G N:Matrix U U ℝ}(hH:H.transpose=H)(hK:K.transpose=K)(h:K*H=1)(hG:G.transpose=G)(p: Ink (U⊕Y))
    (R:Matrix U U ℝ)(hr:IsUnit R.det)(hk:K=R.transpose*N*R)(he:G=R*H*R.transpose)(θ:U→ Ink (U⊕Z))(W:Y→ Ink Z)
    (hL: ∀ i,constantCoeff (θ i)=constantCoeff (noiseLine R i)) :
   Wick Z H ((motionJ θ).det*(raiseE (bodyQ Z K-reroll W θ (bodyQ Y N))*reroll W θ p))= realS R.det * train W (Wick Y G p) := by
  let M i:= noiseLine (Y:=Option Z) R i
  let θ' (i:U): Ink (U⊕Option Z):= M i + path (.inr none)* hideF U Z (θ i-noiseLine R i)
  let W' (i:Y):= hide Z (W i)
  have he' i : constantCoeff (θ' i)=constantCoeff (M i) := by
    have hZ : constantCoeff (hideF U Z (θ i-noiseLine R i))=0 := by
      rw [←coeff_zero_eq_constantCoeff_apply,hideF,coeff_map,coeff_zero_eq_constantCoeff_apply,map_sub,hL]; simp
    unfold θ'; rw [map_add,map_mul,hZ]; ring
  let B:=reroll W' θ'
  let F:=bodyQ (Option Z) K-reroll W' θ' (bodyQ Y N)
  let q:=(motionJ θ').det * (raiseE F * B p)
  have hp : constantCoeff F=0 := local_zero_roll R W' he' hk
  have hv := W_density hH hK h p none θ' W' (jac_unit hr he') (fun i=> latent _) hp
  have bound (x:ℝ): see Z x (Wick (Option Z) H q) = Wick Z H ((motionJ (fun i=> watch U Z x (θ' i))).det * (raiseE
       (bodyQ Z K - reroll W (fun i=> watch U Z x (θ' i)) (bodyQ Y N))*reroll W (fun i=> watch U Z x (θ' i)) p)) := by
    have he (p): watch U Z x (B p)=reroll W (fun i=> watch U Z x (θ' i)) p := by
      have hw i : see Z x (W' i)= W i := arrive ..
      simpa only [RingHom.comp_apply,hw] using DFunLike.congr_fun (watch_comp W' θ' x) p
    unfold q; rw [← watch_wick hH, map_mul, map_mul,watch_jac,
      raise_map _ (by rw [watch_X]; simp) hp,he p,show F=bodyQ (Option Z) K - B (bodyQ Y N) from rfl,map_sub,watch_score,he]
  have hu i : watch U Z 1 (θ' i)= θ i := by simp_rw [θ',M,map_add,map_mul,revisit,watch_line, watch_time]; simp
  have hw i : watch U Z 0 (θ' i)= noiseLine R i := by simp_rw [θ',M,map_add,map_mul,watch_time,watch_line]; simp
  have hg := see_ext (p:=Wick (Option Z) H q) hv 1 0; rw [bound,bound] at hg
  simp_rw [hu,hw,jac_lead] at hg; rw [hg]
  rw [show reroll W (noiseLine R)=railCov R W from rfl,form_rotate W R hk,sub_self]
  have hq : raiseE (0:Ink (U⊕Z))=1 := by
    have hk := raise_change (f:=(0:Ink (U⊕Z))) (by simp)
    apply raise_unique _ hk (by simp); rw [raise_one (by simp),map_one]
  rw [hq,one_mul,←real_alg,←Algebra.smul_def,W_smul,W_linear R W hG hH he,Algebra.smul_def,real_alg]
end YM.WilsonCoeffUV.Blue
