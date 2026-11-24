import YM.FullVolume.Cross
import YM.MatchingLedger.Compass.Deck
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! A signed incoming-coupling chart for the actual adjacent betas of one Run.
Its coefficient is the literal coarse-minus-fine beta difference, not a Plan
prediction. The explicit formula is analytic at zero and maps the actual
positive coarse regulator to the actual fine regulator. That point identity
does not require membership in a chosen inverse-function neighborhood. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunCouplingChart
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open MatchingLedger.Compass.Income
open scoped ContDiff

variable {G : Gauge} (R : Run G) (N p m : ℕ)

def betaDifference : ℝ :=
  R.family.path.β N p m - R.family.path.β N p (m + 1)

def radicand (h : ℝ) : ℝ := 1 - betaDifference R N p m * h ^ 2

def unit (h : ℝ) : ℝ := (Real.sqrt (radicand R N p m h))⁻¹

def incoming (h : ℝ) : ℝ := h * unit R N p m h

private theorem radicand_zero : radicand R N p m 0 = 1 := by
  simp [radicand]

private theorem radicand_contDiff : ContDiff ℝ ω (radicand R N p m) :=
  contDiff_const.sub (contDiff_const.mul (contDiff_id.pow 2))

theorem unit_zero : unit R N p m 0 = 1 := by
  simp [unit, radicand]

theorem unit_analytic : ContDiffAt ℝ ω (unit R N p m) 0 :=
  ((radicand_contDiff R N p m).contDiffAt.sqrt
    (by rw [radicand_zero]; exact one_ne_zero)).inv
      (by rw [radicand_zero, Real.sqrt_one]; exact one_ne_zero)

theorem incoming_zero : incoming R N p m 0 = 0 := by
  simp [incoming]

theorem incoming_analytic : ContDiffAt ℝ ω (incoming R N p m) 0 :=
  contDiffAt_id.mul (unit_analytic R N p m)

theorem incoming_derivative : HasDerivAt (incoming R N p m) 1 0 := by
  have h := ((unit_analytic R N p m).differentiableAt (by simp)).hasDerivAt
  unfold incoming
  simpa only [one_mul, unit_zero, zero_mul, add_zero] using
    (hasDerivAt_id' (0 : ℝ)).fun_mul h

/-- The radicand is strictly positive at the actual coarse regulator because
both represented betas are positive. The identity retains both scale indices. -/
theorem coarse_radicand (hm : m < N) :
    radicand R N p m (regulatorRun R.family N p m) =
      R.family.path.β N p (m + 1) / R.family.path.β N p m := by
  have hc := Weather.iceborn R.family R.makes hm.le p
  have hsq : regulatorRun R.family N p m ^ 2 =
      (R.family.path.β N p m)⁻¹ := by
    unfold regulatorRun
    rw [inv_pow, Real.sq_sqrt hc.le]
  rw [radicand, hsq, betaDifference]
  field_simp [hc.ne']; ring

/-- Exact actual-to-actual coupling conversion; no predicted beta equality. -/
theorem incoming_coarse (hm : m < N) :
    incoming R N p m (regulatorRun R.family N p m) =
      regulatorRun R.family N p (m + 1) := by
  have hc := Weather.iceborn R.family R.makes hm.le p
  have hf := Weather.iceborn R.family R.makes (Nat.succ_le_of_lt hm) p
  change regulatorRun R.family N p m *
      (Real.sqrt (radicand R N p m (regulatorRun R.family N p m)))⁻¹ = _
  rw [coarse_radicand R N p m hm]
  unfold regulatorRun
  rw [Real.sqrt_div' _ hc.le]
  field_simp [(Real.sqrt_pos.mpr hc).ne', (Real.sqrt_pos.mpr hf).ne']

/-- The compensating unit at the actual point is the literal regulator ratio. -/
theorem unit_coarse (hm : m < N) :
    unit R N p m (regulatorRun R.family N p m) =
      regulatorRun R.family N p (m + 1) / regulatorRun R.family N p m := by
  have hc := Weather.runs_pos R.family R.makes hm.le p
  apply (eq_div_iff hc.ne').2
  calc
    unit R N p m (regulatorRun R.family N p m) *
        regulatorRun R.family N p m =
      incoming R N p m (regulatorRun R.family N p m) := mul_comm _ _
    _ = _ := incoming_coarse R N p m hm

end YM.Integration.ActualRunCouplingChart
end
