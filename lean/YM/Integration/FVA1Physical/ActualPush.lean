import YM.SectorNext.VACUUM_NORMALIZATION.Stripped

/-! Error propagation for the vacuum-normalized physical block map. -/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical

open MeasureTheory RG Lattice Wilson
open scoped BigOperators

variable {G : Gauge} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Conditional transport at one blocking step of the selected finite-volume history.
Both vacuum densities and the coupling come from the same history. -/
def conditionalPush (A : History G) (N p m : ℕ)
    (F : Config G (A.S.side (m + 1) p) → E) (V : Config G (A.S.side m p)) : E :=
  ((A.rep N p m).eval V)⁻¹ • (A.levels.clock.op m p).push (A.β N p (m + 1))
    (fun U => (A.rep N p (m + 1)).eval U • F U) V

/-- A uniform bound on an evaluated error passes to every coarse field with coefficient one. -/
theorem conditionalPush_bound (A : History G) (h : A.Selected) (N p m : ℕ) (hm : m < N)
    (F : Config G (A.S.side (m + 1) p) → E) (b : ℝ) (hF : ∀ U, ‖F U‖ ≤ b)
    (V : Config G (A.S.side m p)) : ‖conditionalPush A N p m F V‖ ≤ b := by
  let S := A.levels.clock.op m p
  let β := A.β N p (m + 1)
  let w := (A.rep N p (m + 1)).eval
  let μ := prior G (A.S.side (m + 1) p)
  have hker : S.IsKernel β G := A.levels.transition_mass m p β
  have hw : Integrable w μ :=
    ((A.rep N p (m + 1)).envelope (h.represents N p (m + 1) hm).good).integrable _
  have hweight : Integrable (fun U => S.density β U V * w U) μ :=
    StepData.push_slice hker V w hw
  have hmass : (∫ U, S.density β U V * w U ∂μ) = (A.rep N p m).eval V :=
    (congrFun (h.steps N p m hm).1 V).symm
  have hpos := SectorNext.Vacuum.strictly A h N p m hm.le V
  have hbound : ‖S.push β (fun U => w U • F U) V‖ ≤ (A.rep N p m).eval V * b := by
    change ‖∫ U, S.density β U V • (w U • F U) ∂μ‖ ≤ _
    rw [← hmass, ← integral_mul_const]
    apply norm_integral_le_of_norm_le (hweight.mul_const b)
    refine Filter.Eventually.of_forall fun U => ?_
    have hk := hker.positive U V
    have hw' : 0 ≤ w U := A.nonnegative h N p (m + 1) hm U
    simp only [norm_smul, Real.norm_of_nonneg hk, Real.norm_of_nonneg hw', ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (hF U) (mul_nonneg hk hw')
  unfold conditionalPush
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  calc
    _ ≤ ((A.rep N p m).eval V)⁻¹ * ((A.rep N p m).eval V * b) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hpos.le)
    _ = b := by rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

/-- Stagewise evaluated defects telescope on the actual trajectory. The local costs may
depend on the scale and do not acquire volume or vacuum factors during iteration. -/
theorem accumulated_physical_error (A : History G) (h : A.Selected) (N p : ℕ)
    (F : (m : ℕ) → Config G (A.S.side m p) → E) (b : ℝ) (cost : ℕ → ℝ)
    (top : ∀ U, ‖F N U‖ ≤ b)
    (defect : ∀ m < N, ∀ V, ‖F m V - conditionalPush A N p m (F (m + 1)) V‖ ≤ cost m)
    (m : ℕ) (hm : m ≤ N) (V : Config G (A.S.side m p)) :
    ‖F m V‖ ≤ b + ∑ j ∈ Finset.Ico m N, cost j := by
  induction hm using Nat.decreasingInduction with
  | self => simpa using top V
  | of_succ k hk ih =>
    have bound := conditionalPush_bound A h N p k hk (F (k + 1)) _ ih V
    have split := norm_add_le (F k V - conditionalPush A N p k (F (k + 1)) V)
      (conditionalPush A N p k (F (k + 1)) V)
    rw [sub_add_cancel] at split
    rw [← Finset.insert_Ico_add_one_left_eq_Ico hk, Finset.sum_insert (by simp)]
    linarith [defect k hk V]

end YM.Integration.FVA1Physical
