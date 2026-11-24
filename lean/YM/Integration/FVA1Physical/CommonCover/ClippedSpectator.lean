import YM.Integration.FVA1Physical.CommonCover.ClippedCrossing

/-! A gross cap on the error allows a single inverse of the original vacuum
gas to pay for an arbitrary correlated square-integrable spectator. Only the
part of the field space where a crossing can occur needs to be charged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Crossing
open MeasureTheory Set

theorem tested_sqrt_charge {Z : Type*} [MeasurableSpace Z] (law : Measure Z)
    (Y : Z → ℂ) (y2 : MemLp Y 2 law) (f : Z → ℝ) (fi : Integrable f law)
    (fp : ∀ z, 0 ≤ f z) :
    Integrable (fun z => ‖Y z‖ * Real.sqrt (f z)) law ∧
      (∫ z, ‖Y z‖ * Real.sqrt (f z) ∂law) ≤
        Real.sqrt (∫ z, ‖Y z‖ ^ 2 ∂law) * Real.sqrt (∫ z, f z ∂law) := by
  let h := fun z => Real.sqrt (f z)
  have hm : AEStronglyMeasurable h law := Real.continuous_sqrt.comp_aestronglyMeasurable fi.1
  have sq (z : Z) : h z ^ 2 = f z := Real.sq_sqrt (fp z)
  have normsq (z : Z) : ‖h z‖ ^ 2 = f z := by
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), sq]
  have h2 : MemLp h 2 law := (memLp_two_iff_integrable_sq_norm hm).2 (by
    simpa only [normsq] using fi)
  have l : MemLp (fun z => ‖Y z‖) (ENNReal.ofReal 2) law := by
    norm_num
    exact y2.norm
  have r : MemLp h (ENNReal.ofReal 2) law := by norm_num; exact h2
  have cs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all law (fun z => norm_nonneg (Y z)))
    (ae_of_all law (fun z => Real.sqrt_nonneg (f z))) l r
  refine ⟨y2.norm.integrable_mul h2, ?_⟩
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, Real.sq_sqrt (fp _)] using cs

/-- Single-inverse payment for the clipped physical fee. The three incoming
raw gas rows are bounded before division. The constant may be restricted
to an arbitrary measurable crossing event by bounding the spent wallet there. -/
theorem clipped_first_moment {Z : Type*} [MeasurableSpace Z] (law : Measure Z)
    (Y : Z → ℂ) (y2 : MemLp Y 2 law) (ν W a b : Z → ℝ) (M κ : ℝ)
    (gas : ∀ z, 0 < ν z) (unit : ∀ z, ν z ≤ 1) (cross : ∀ z, 0 ≤ W z)
    (gross : 0 ≤ M) (aa : ∀ z, 0 ≤ a z) (bb : ∀ z, 0 ≤ b z)
    (ha : ∀ z, a z ≤ κ) (hb : ∀ z, b z ≤ κ)
    (f : Z → ℝ) (fi : Integrable f law)
    (charge : ∀ z, (M^5*(2*W z*(M+(1+κ)^2)))^((3:ℝ)⁻¹) / ν z ≤ f z) :
    let h := fun z => Real.sqrt (f z)
    (∀ z, min M (invoice (ν z) (W z) M (a z) (b z)) ≤ h z) ∧
    Integrable (fun z => ‖Y z‖ * h z) law ∧
    (∫ z, ‖Y z‖ * h z ∂law) ≤
      Real.sqrt (∫ z, ‖Y z‖ ^ 2 ∂law) * Real.sqrt (∫ z, f z ∂law) := by
  intro h
  have point (z : Z) : (min M (invoice (ν z) (W z) M (a z) (b z)))^2 ≤ f z :=
    ((le_div_iff₀ (gas z)).2 (clipped_square (gas z) (unit z) (cross z) gross
      (aa z) (bb z) (ha z) (hb z))).trans (charge z)
  refine ⟨fun z => ?_, tested_sqrt_charge law Y y2 f fi (fun z => (sq_nonneg _).trans (point z))⟩
  exact (le_abs_self _).trans ((Real.sqrt_sq_eq_abs _).symm.le.trans (Real.sqrt_le_sqrt (point z)))

end YM.Integration.FVA1Physical.Crossing
