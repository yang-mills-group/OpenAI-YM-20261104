import YM.RG3.Law.Sample
import YM.Integration.ActualMarkedDensity

/-! The full conditional law of the existing physical trajectory. The vacuum
is identified from `C.Makes`, rather than supplied as a normalization premise.
The contraction below is a value estimate. It does not assert localization
of conditional expectations or the small, differentiated comparison remainder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Lattice Wilson RG MeasureTheory
open scoped BigOperators Classical

variable {G : Gauge} (C : Family G) (N p m : ℕ)

/-- The full incoming density and actual transition, divided by the actual
outgoing density. No independent measure or representation is chosen. -/
def actualConditionalDensity (V : Config G (C.side m p))
    (U : Config G (C.side (m+1) p)) : ℝ :=
  (C.path.levels.clock.op m p).density (C.path.β N p (m+1)) U V *
    (C.path.rep N p (m+1)).eval U / (C.path.rep N p m).eval V

variable {N p m} (hC : C.Makes) (hm : m < N)
include hC hm

theorem actualConditionalDensity_nonneg (V : Config G (C.side m p))
    (U : Config G (C.side (m+1) p)) :
    0 ≤ actualConditionalDensity C N p m V U :=
  div_nonneg (mul_nonneg ((C.path.levels.clock.op m p).density_positive ..)
    (Multi.AxisShift.chosen_positive hC.wilson hm U).le)
    (Multi.AxisShift.chosen_positive hC.wilson hm.le V).le

theorem actualConditionalDensity_integrable (V : Config G (C.side m p)) :
    Integrable (actualConditionalDensity C N p m V) (prior G _) := by
  have hK := (C.path.levels.clock.op m p).isKernel
    (C.path.levels.blocks m p).branches (C.path.β N p (m+1))
  have hI := ((C.path.rep N p (m+1)).envelope
    (hC.wilson.represents N p (m+1) hm).good).integrable (prior G _)
  exact (StepData.push_slice hK V _ hI).div_const _

/-- Probability normalization is proved from the selected history's exact step. -/
theorem actualConditionalDensity_total (V : Config G (C.side m p)) :
    (∫ U, actualConditionalDensity C N p m V U ∂prior G _) = 1 := by
  unfold actualConditionalDensity
  rw [integral_div, ← RG3.Law.common hC hm V,
    RG3.Law.denom_eq hC hm.le V]
  exact div_self (Multi.AxisShift.chosen_positive hC.wilson hm.le V).ne'

omit hC hm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual normalized one-step expectation, including the full vacuum. -/
def actualAverage (F : Config G (C.side (m+1) p) → E)
    (V : Config G (C.side m p)) : E :=
  ∫ U, actualConditionalDensity C N p m V U • F U ∂prior G _

/-- Exact supplier-to-consumer identification; no denominator estimate is an input. -/
theorem actualAverage_push (F : Config G (C.side (m+1) p) → E)
    (V : Config G (C.side m p)) :
    actualAverage C (N := N) F V = ((C.path.rep N p m).eval V)⁻¹ •
      (C.path.levels.clock.op m p).push (C.path.β N p (m+1))
        (fun U => (C.path.rep N p (m+1)).eval U • F U) V := by
  unfold actualAverage actualConditionalDensity StepData.push
  rw [← integral_smul]
  apply integral_congr_ae
  exact ae_of_all _ fun U => by
    dsimp only
    rw [div_eq_mul_inv, mul_comm (_ * _) _, mul_smul, mul_smul]

include hC hm

theorem actualAverage_integrable
    {F : Config G (C.side (m+1) p) → E} {B : ℝ}
    (hF : AEStronglyMeasurable F (prior G _)) (hB : ∀ U, ‖F U‖ ≤ B)
    (V : Config G (C.side m p)) :
    Integrable (fun U => actualConditionalDensity C N p m V U • F U)
      (prior G _) := by
  have hI := actualConditionalDensity_integrable C hC hm V
  apply (hI.mul_const B).mono' (hI.aestronglyMeasurable.smul hF)
  filter_upwards [] with U
  change ‖actualConditionalDensity C N p m V U • F U‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg (actualConditionalDensity_nonneg C hC hm V U)]
  exact mul_le_mul_of_nonneg_left (hB U) (actualConditionalDensity_nonneg C hC hm V U)

/-- No partition-function, volume, or test-space dimension loss. -/
theorem actualAverage_norm_le
    {F : Config G (C.side (m+1) p) → E} {B : ℝ}
    (hB : ∀ U, ‖F U‖ ≤ B) (V : Config G (C.side m p)) :
    ‖actualAverage C (N := N) F V‖ ≤ B := by
  have h := norm_integral_le_of_norm_le
    ((actualConditionalDensity_integrable C hC hm V).mul_const B)
    (ae_of_all _ fun U => show ‖actualConditionalDensity C N p m V U • F U‖ ≤
      actualConditionalDensity C N p m V U * B from by
        rw [norm_smul, Real.norm_of_nonneg (actualConditionalDensity_nonneg C hC hm V U)]
        exact mul_le_mul_of_nonneg_left (hB U) (actualConditionalDensity_nonneg C hC hm V U))
  exact h.trans_eq (by rw [integral_mul_const, actualConditionalDensity_total C hC hm V, one_mul])

theorem actualAverage_const [CompleteSpace E] (v : E) (V : Config G (C.side m p)) :
    actualAverage C (N := N) (fun _ => v) V = v := by
  unfold actualAverage
  rw [integral_smul_const, actualConditionalDensity_total C hC hm V, one_smul]

end YM.Integration
