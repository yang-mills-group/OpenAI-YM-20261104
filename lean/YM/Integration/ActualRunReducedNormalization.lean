import YM.Integration.ActualRunCoarseReadout

/-! Exact removal of the field-independent scalar from the original Run.
The complete actual action and forced gas remain in the density. Its mass
comes from the original Wilson partition; no lower bound on a replacement
partition or integrability of an arbitrary reciprocal is assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunReducedNormalization

open MeasureTheory Lattice Wilson RG PhysicalNext.Repeat.Legato

variable {G : Gauge} (R : Run G) (N period m : ℕ)
local notation "X" => R.family.path.rep N period m

def density (U : Config G (R.family.side m period)) : ℝ :=
  Real.exp (-(X).scalar) * (X).eval U

def mass : ℝ :=
  ∫ U, density R N period m U ∂prior G (R.family.side m period)

def average (F : Config G (R.family.side m period) → ℂ) : ℂ :=
  (mass R N period m : ℂ)⁻¹ *
    ∫ U, (density R N period m U : ℂ) * F U
      ∂prior G (R.family.side m period)

/-- Every original action and gas term survives scalar cancellation. -/
theorem density_action (U : Config G (R.family.side m period)) :
    density R N period m U =
      Real.exp (-(X).path.inChannels (X).clip (X).p (X).beta U -
        (X).activities.additive (X).p U) * (X).activities.gas (X).p U := by
  have he : -(X).scalar + (X).exponent U =
      -(X).path.inChannels (X).clip (X).p (X).beta U - (X).activities.additive (X).p U := by
    unfold Rep.scalar Rep.exponent
    ring
  change Real.exp (-(X).scalar) *
    (Real.exp ((X).exponent U) * (X).activities.gas (X).p U) = _
  rw [← mul_assoc, ← Real.exp_add, he]

/-- The removed factor is nonzero and reconstructs the full original density. -/
theorem density_factor (U : Config G (R.family.side m period)) :
    (X).eval U = Real.exp (X).scalar * density R N period m U := by
  unfold density
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- Integrability is inherited from the actual retained representation. -/
theorem density_integrable (hm : m ≤ N) :
    Integrable (density R N period m) (prior G (R.family.side m period)) :=
  (ActualCoveredNormalization.same_run_reference R N period m hm).2.1.const_mul _

/-- The denominator is exactly the same original Wilson partition with the
same single scalar removed. -/
theorem mass_eq (hm : m ≤ N) :
    mass R N period m = Real.exp (-(X).scalar) *
      partition G (R.family.side N period) (R.family.beta N period) := by
  unfold mass density
  rw [integral_const_mul,
    (ActualCoveredNormalization.same_run_reference R N period m hm).2.2]

theorem mass_pos (hm : m ≤ N) : 0 < mass R N period m := by
  rw [mass_eq R N period m hm]
  exact mul_pos (Real.exp_pos _) (partition_pos _)

/-- The same scalar cancels in the numerator and denominator for every full
complex observable. No pointwise replacement of the original density occurs. -/
theorem average_eq (hm : m ≤ N)
    (F : Config G (R.family.side m period) → ℂ) :
    average R N period m F =
      ActualRunCoarseReadout.expectation R N period m F := by
  unfold average
  rw [mass_eq R N period m hm]
  unfold density ActualRunCoarseReadout.expectation ActualRunCoarseReadout.readout
  simp_rw [Complex.ofReal_mul, mul_assoc]
  rw [integral_const_mul]
  let c : ℂ := Real.exp (-(X).scalar)
  let z : ℂ := partition G (R.family.side N period) (R.family.beta N period)
  let b : ℂ := ∫ U, ((X).eval U : ℂ) * F U
    ∂prior G (R.family.side m period)
  change (c * z)⁻¹ * (c * b) = z⁻¹ * b
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  rw [mul_inv_rev, mul_assoc, ← mul_assoc c⁻¹ c b, inv_mul_cancel₀ hc, one_mul]

/-- At the physical endpoint the normalized integral is the original Wilson
expectation, with its genuine integrability condition. -/
theorem original_average
    (F : Config G (R.family.side N period) → ℂ)
    (hF : Integrable F (law G (R.family.side N period) (R.family.beta N period))) :
    average R N period N F = R.family.omega N period F := by
  rw [average_eq R N period N le_rfl]
  exact ActualRunCoarseReadout.original_readout R N period F hF

end YM.Integration.ActualRunReducedNormalization
end
