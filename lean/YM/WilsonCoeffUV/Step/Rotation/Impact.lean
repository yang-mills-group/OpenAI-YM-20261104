import YM.WilsonCoeffUV.Step.Rotation.Angle
/-!
# Aux: leading-impact and determinant change in different precision W calculation.
Need only ONE invertible; the other follows from congruence.
Specializes W_covariance; no estimate on real integrals with additional masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue.Freedom
open Matrix Function PowerSeries Filter
open scoped BigOperators Topology ContDiff
variable {X Y Z:Type*}[Fintype X][DecidableEq X]
-- Compare leading using the same argument as `Auxiliary.strike_leading`,
-- here hypothesis on OLD precision only (target congruence implies invertible).
section lead
variable [Fintype Z]
omit [Fintype X] [DecidableEq X] [Fintype Z] in
private lemma moment_head {x:X}{A B:Ink (X⊕Z)}(h:constantCoeff A=constantCoeff B) : constantCoeff (brush (.inl x) A)=constantCoeff (brush (.inl x) B):= by rw [←coeff_zero_eq_constantCoeff_apply,←coeff_zero_eq_constantCoeff_apply,brush,blot_apply,blot_apply]; simp only [coeff_zero_eq_constantCoeff_apply,h]
omit [Fintype Z] in
private lemma callH (a:X→Ink (X⊕Z))(u:Y→Ink Z)(K:Matrix X X ℝ)(hk:K.transpose=K)(j:X)[Fintype Y] : brush (.inl j) (reroll u a (bodyQ Y K))= ∑ i:X, brush (.inl j) (a i)*∑ b: X,K i b • a b := by
  rw [reroll,reroutes,Fintype.sum_sum_type]; simp only [Sum.elim_inl,Sum.elim_inr,Function.comp_apply, up_vacant,zero_mul, Finset.sum_const_zero,add_zero]
  change ∑ i, _ * reroll u a _= _
  apply Finset.sum_congr rfl; intro i _; rw [body_derived K hk, moment_const]
omit [DecidableEq X] in
private lemma pull_lead (R:Matrix X X ℝ)(q:Lawn (X⊕Z)→ Lawn X)(hR:R=edgeM q 0)(i j:X)(hq:Green q)(hz:q 0=0) :
    constantCoeff (brush (Sum.inl j) (spool q i))=MvPolynomial.C (R i j):= by rw [spool_ext q i hq hz (Sum.inl j), jet_lead, hR]; rfl

lemma both_leading (u:Y→Ink Z)[Fintype Y]
   (q:Lawn (X⊕Z)→ Lawn X)(hq:Green q)(hz:q 0=0) (K N:Matrix X X ℝ)(hK:K.transpose=K)(hN:N.transpose=N)(hk:IsUnit K.det)
   (R:Matrix X X ℝ)(hR:R=edgeM q 0)(hr:IsUnit R.det)
   (c d:Ink Z)
   (hc:constantCoeff (bodyQ Z K + holdUp X c)=constantCoeff (reroll u (spool q) (bodyQ Y N)+ holdUp X d)) :
   K= R.transpose*N*R ∧ ∀ i, constantCoeff (spool q i)=constantCoeff (noiseLine R i) := by
  let v:=spool q
  -- gradient one
  have first (j:X): constantCoeff (slopeQ Z K j)=constantCoeff (∑ i:X, brush (.inl j) (v i)*(∑ b:X,N i b • v b)) := by
    have h:= moment_head (x:=j) hc; rw [map_add (brush _),map_add (brush _),up_vacant,up_vacant,add_zero,add_zero,body_derived _ hK,callH _ _ _ hN] at h; exact h
  let A j:= constantCoeff (v j)
  let C:=MvPolynomial.C (σ:=X⊕Z) (R:=ℝ)
  have S j {a: Ink (X⊕Z)}: constantCoeff (brush (Sum.inl j) a)=MvPolynomial.pderiv (.inl j) (constantCoeff a) := by rw [←coeff_zero_eq_constantCoeff_apply,←coeff_zero_eq_constantCoeff_apply,brush,blot_apply]
  have e₁ j : ∑ i, K j i • MvPolynomial.X (Sum.inl (β:=Z) i) = ∑ i, C (R i j) * ∑ b:X, N i b • A b := by
    have H:=first j; simp_rw [slopeQ,map_sum,constantCoeff_smul,path, constantCoeff_C,map_mul,map_sum,constantCoeff_smul, show ∀ i,constantCoeff (brush (.inl j) (v i))=C (R i j) from fun i=>pull_lead R q hR i j hq hz] at H; exact H
  have hh (i j) : MvPolynomial.pderiv (.inl j) (A i)= C (R i j):= (S j).symm.trans (pull_lead R q hR i j hq hz)
  have e₂ : K= R.transpose*N*R := by
    ext1 i j
    classical
    have he:=congrArg (MvPolynomial.pderiv (Sum.inl j)) (e₁ i); simp_rw [map_sum, Derivation.map_smul,MvPolynomial.pderiv_mul, map_sum,Derivation.map_smul,hh] at he
    simp only [C,MvPolynomial.pderiv_C,zero_mul,zero_add] at he
    rw [Finset.sum_eq_single j] at he;
    · simp only [MvPolynomial.pderiv_X_self, Algebra.smul_def,mul_one,MvPolynomial.algebraMap_eq] at he
      apply MvPolynomial.C_injective (σ:=X⊕Z) (R:=ℝ)
      rw [he,Matrix.mul_apply]; simp only [Matrix.mul_apply,transpose_apply,map_sum, Finset.mul_sum, Finset.sum_mul,map_mul]
      rw [Finset.sum_comm]; simp_rw [mul_assoc]
    · intro b _ hb; rw [MvPolynomial.pderiv_X_of_ne (by simpa), smul_zero]
    simp
  refine ⟨e₂,?_⟩
  let B (a:X): POL (X⊕Z) := MvPolynomial.X (.inl a)
  have h : K.map C *ᵥ B= (R.map C).transpose *ᵥ ((N.map C)*ᵥ A) := by
    ext1 i; simpa only [mulVec,dotProduct, Matrix.map_apply,transpose_apply,C, Algebra.smul_def,MvPolynomial.algebraMap_eq] using e₁ i
  have e : K.map C=(R.map C).transpose*(N.map C)*(R.map C) := by
    conv_lhs=>rw [e₂];
    simp_rw [Matrix.map_mul]; rfl
  conv_lhs at h=> rw [e,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
  let D := (R.map C).transpose * (N.map C)
  have hn: IsUnit N.det := by
    rw [e₂,Matrix.det_mul,Matrix.det_mul] at hk; apply isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hk)
  have hu : IsUnit D.det:= by unfold D; rw [Matrix.det_mul, Matrix.det_transpose]; change IsUnit ((C.mapMatrix R).det * (C.mapMatrix N).det); rw [← RingHom.map_det, ← RingHom.map_det]; exact (hr.map C).mul (hn.map C)
  conv_lhs at h=> rw [Matrix.mulVec_mulVec]
  conv_rhs at h=> rw [Matrix.mulVec_mulVec]
  have eq: A = (R.map C)*ᵥ B := by
    exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hu) h.symm
  intro i
  change A i=_; rw [eq]; simp_rw [noiseLine,map_sum,constantCoeff_smul,path,constantCoeff_C]; simp only [B,dotProduct,mulVec,Matrix.map_apply,C, Algebra.smul_def,MvPolynomial.algebraMap_eq]
end lead
end YM.WilsonCoeffUV.Blue.Freedom
