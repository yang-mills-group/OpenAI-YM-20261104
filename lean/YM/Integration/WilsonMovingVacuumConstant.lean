import YM.Integration.WilsonConditionalTaylorWick
import YM.Integration.WilsonMovingExponentialConvention

/-! Removing a field-independent vacuum series from the previous action does
not change any normalized numerical marked coefficient. Both the genuine
numerator and its denominator acquire the same complete exponential. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingVacuumConstant
open Matrix PowerSeries FormalBulk08 Series MSbar.Cacao WilsonConditionalTaylorWick
open scoped Classical BigOperators Matrix
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable (B : Matrix J I ℝ) (x : J→ℝ) (Q : Matrix I I ℝ)

def scalar (I : Type) (c : PowerSeries ℝ) : PowerSeries (MvPolynomial I ℝ) :=
  PowerSeries.map MvPolynomial.C c

private theorem taken {A : Type} [CommRing A] [Algebra ℝ A] (E : A →ₗ[ℝ] ℝ)
    (c : PowerSeries ℝ) (f : PowerSeries A) :
    beam E (PowerSeries.map (algebraMap ℝ A) c * f) = c * beam E f := by
  ext n
  simp only [coeff_beam,PowerSeries.coeff_mul,map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [PowerSeries.coeff_map, ← Algebra.smul_def, map_smul, smul_eq_mul]

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem paid (c : PowerSeries ℝ) (T : PowerSeries (MvPolynomial J ℝ)) :
    contract B x Q (scalar J c*T)=c*contract B x Q T := by
  have spot : PowerSeries.map (WilsonMovingWickCoefficient.affine B x).toRingHom (scalar J c) =
      scalar I c := by
    apply PowerSeries.ext
    intro i
    simp only [scalar,PowerSeries.coeff_map]
    exact (WilsonMovingWickCoefficient.affine B x).commutes (coeff i c)
  unfold contract
  rw [map_mul,spot]
  exact taken (Wick.moment Q) c _

omit [Fintype J] [DecidableEq J] in
theorem action (f : PowerSeries (MvPolynomial J ℝ)) (h : Kind f)
    (c : PowerSeries ℝ) (hc : coeff 0 c=0) :
    Spring (f+scalar J c)=scalar J (Series.expan c)*Spring f := by
  have cs : coeff 0 (scalar J c)=0 := by simp only [scalar,PowerSeries.coeff_map,hc,map_zero]
  have hs : Kind (f+scalar J c) := by rw [Kind,map_add,show coeff 0 f=0 from h,cs,add_zero]
  rw [← WilsonMovingExponentialConvention.exp _ hs, ← Series.expan_mul h cs,
    ← WilsonMovingExponentialConvention.exp f h, mul_comm]
  simp only [scalar,Series.map_expan _ hc]

private theorem normalized (w z n : PowerSeries ℝ) (hw : coeff 0 w=1) (hz : coeff 0 z=1) :
    (w*n)*PowerSeries.invOfUnit (w*z) 1=n*PowerSeries.invOfUnit z 1 := by
  have u : z * PowerSeries.invOfUnit z 1=1 :=
    PowerSeries.mul_invOfUnit _ _ (by rw [← coeff_zero_eq_constantCoeff_apply,hz];rfl)
  have v : (w*z) * PowerSeries.invOfUnit (w*z) 1=1 :=
    PowerSeries.mul_invOfUnit _ _ (by rw [map_mul,← coeff_zero_eq_constantCoeff_apply,hw,
      ← coeff_zero_eq_constantCoeff_apply,hz,one_mul];rfl)
  have r : (n*PowerSeries.invOfUnit z 1)*(w*z)=w*n := by
    calc
      _ = (w*n)*(z*PowerSeries.invOfUnit z 1) := by ring
      _ = _ := by rw [u,mul_one]
  rw [← r,mul_assoc,v,mul_one]

omit [Fintype J] [DecidableEq J] in
theorem invariant (sym : Q.IsSymm) (pos : Q.PosDef) (T f : PowerSeries (MvPolynomial J ℝ)) (h : Kind f)
    (c : PowerSeries ℝ) (hc : coeff 0 c=0) :
    quotient B x Q (f+scalar J c) T=quotient B x Q f T := by
  unfold quotient
  rw [action f h c hc, mul_left_comm T,paid,paid]
  apply normalized
  · exact Series.expan_zero hc
  · unfold contract
    rw [← WilsonMovingWickCoefficient.complete B x Q sym pos.posSemidef]
    exact WilsonMovingGaussianResponse.first Q B x (Spring f) (covers h)

end YM.Integration.WilsonMovingVacuumConstant
end
