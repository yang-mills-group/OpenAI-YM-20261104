import YM.RG.Bounded

noncomputable section
namespace YM.Integration.WilsonNormalizedLocalGibbs
open MeasureTheory Filter Function Real
open scoped Topology Classical

variable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)

/-- Comparison of the two actual normalizers on one integration domain.
    No lower bound on an individual marked numerator is used. -/
theorem compare {a δ : ℝ} (ha : 0 < a) (d : 0 ≤ δ) {P W : Ω→ℝ} {H : Ω→ℂ}
    (pInt : Integrable P ν) (wInt : Integrable W ν) (hp : 0 < ∫ z,P z ∂ν)
    (tested : Integrable (fun z=>P z*‖H z‖) ν)
    (range : ∀ᵐ z ∂ν, 0 ≤ P z ∧ exp (-δ)*a*P z ≤ W z ∧ W z ≤ exp δ*a*P z) :
    ‖∫ z, (W z/(∫ t,W t ∂ν)-P z/(∫ t,P t ∂ν)) • H z ∂ν‖ ≤
      (exp (2*δ)-exp (-(2*δ)))/(∫ z,P z ∂ν)*(∫ z,P z*‖H z‖ ∂ν) := by
  let p := ∫ t,P t ∂ν
  let w := ∫ t,W t ∂ν
  let A := exp (-δ)*a
  let B := exp δ*a
  have Ap : 0 < A := mul_pos (exp_pos _) ha
  have Bp : 0 < B := mul_pos (exp_pos _) ha
  have lo : A*p ≤ w := by
    rw [show A*p = ∫ z, A*P z ∂ν from (integral_const_mul ..).symm]
    exact integral_mono_ae (pInt.const_mul A) wInt (range.mono fun z h=>h.2.1)
  have hi : w ≤ B*p := by
    rw [show B*p = ∫ z, B*P z ∂ν from (integral_const_mul ..).symm]
    exact integral_mono_ae wInt (pInt.const_mul B) (range.mono fun z h=>h.2.2)
  have wp : 0 < w := (mul_pos Ap hp).trans_le lo
  have ratio_hi : B/A = exp (2*δ) := by
    rw [show 2*δ = δ-(-δ) by ring,exp_sub]
    dsimp [A,B]; field_simp
  have ratio_lo : A/B = exp (-(2*δ)) := by
    rw [show -(2*δ) = -δ-δ by ring,exp_sub]
    dsimp [A,B]; field_simp
  have small : exp (-(2*δ)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have big : 1 ≤ exp (2*δ) := one_le_exp (by linarith)
  have estimate : ∀ᵐ z ∂ν,
      |W z/w-P z/p| ≤ (exp (2*δ)-exp (-(2*δ)))*(P z/p) := range.mono fun z h=>by
    have pz : 0 ≤ P z/p := div_nonneg h.1 hp.le
    have wz : 0 ≤ W z := (mul_nonneg Ap.le h.1).trans h.2.1
    have upper : W z/w ≤ exp (2*δ)*(P z/p) := by
      calc W z/w ≤ (B*P z)/(A*p) := div_le_div₀ (mul_nonneg Bp.le h.1) h.2.2 (mul_pos Ap hp) lo
           _ = (B/A)*(P z/p) := by ring
           _ = _ := by rw [ratio_hi]
    have lower : exp (-(2*δ))*(P z/p) ≤ W z/w := by
      rw [←ratio_lo]
      calc (A/B)*(P z/p) = (A*P z)/(B*p) := by ring
           _ ≤ W z/w := div_le_div₀ wz h.2.1 wp hi
    have m1 := mul_le_mul_of_nonneg_right small pz
    have m2 := mul_le_mul_of_nonneg_right big pz
    exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  apply (norm_integral_le_of_norm_le (tested.const_mul ((exp (2*δ)-exp (-(2*δ)))/p))
    (estimate.mono fun z hz=>?_)).trans_eq (integral_const_mul ..)
  rw [norm_smul,Real.norm_eq_abs]
  calc |W z/w-P z/p| * ‖H z‖ ≤ ((exp (2*δ)-exp (-(2*δ)))*(P z/p))*‖H z‖ :=
          mul_le_mul_of_nonneg_right hz (norm_nonneg _)
       _ = _ := by ring

end YM.Integration.WilsonNormalizedLocalGibbs
