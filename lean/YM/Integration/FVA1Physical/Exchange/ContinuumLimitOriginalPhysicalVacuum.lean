import YM.Integration.FVA1Physical.Exchange.ContinuumLimitOriginalSignedForest
import YM.SectorNext.VACUUM_NORMALIZATION.Stripped

/-! The quiet part of a fully marked density is the unmarked interacting
density on the original finite history. Transporting the former gives
exactly the latter at the receiving scale and is strictly positive there. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.OriginalMixedWilson
open Finset Filter Function MeasureTheory RG Wilson Gauge Precision Tree Lattice Exterior
open Next.SectorChange PowerSeries PertExtension.Series Comparison.RG02 Order Marker Multi
open Integral Actual Push.SectorMeasure CommonCover.JetCumulants Extra.Trajectories
open scoped Topology BigOperators Classical

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {R : Census I}

omit [Fintype I] in
theorem push_quiet_real {c f : Side} (S : StepData c f) (β : ℝ)
    (incoming : Config G f → Poly R) (vac : Config G f → ℝ)
    (hquiet : ∀ U, (incoming U).part R.quiet = (vac U : ℂ)) (V : Config G c) :
    (Actual.Push S β incoming V).part R.quiet = (S.push β vac V : ℝ) := by
  rw [Actual.grades]
  change S.push β (Actual.atMark R.quiet incoming) V = _
  have eq : Actual.atMark R.quiet incoming = fun U => (vac U : ℂ) := funext hquiet
  rw [eq,StepData.push,StepData.push]
  simp_rw [Complex.real_smul, ←Complex.ofReal_mul]
  exact integral_ofReal

variable (H : History G) (hs : H.Selected) {N n j : ℕ} (step : j < N)
local notation "S" => H.levels.clock.op j n
local notation "fine" => H.rep N n (j+1)
local notation "coarse" => H.rep N n j

include hs step
omit [Fintype I] in
theorem measured_quiet (incoming : Config G (H.S.side (j+1) n) → Poly R)
    (hquiet : ∀ U, (incoming U).part R.quiet = ((fine).eval U : ℂ))
    (V : Config G (H.S.side j n)) :
    (Actual.Push S (fine).beta incoming V).part R.quiet = ((coarse).eval V : ℂ) ∧
    0 < (coarse).eval V := by
  refine ⟨(push_quiet_real S (fine).beta incoming (fine).eval hquiet V).trans ?_,
    SectorNext.Vacuum.strictly H hs N n j step.le V⟩
  exact congrArg Complex.ofReal (congrFun (hs.steps N n j step).1 V).symm

/-- Any incoming complex log germ with zero quiet component is admitted,
including mixed modes and all inherited positions. -/
theorem measured_log_density (φ : Config G (H.S.side (j+1) n) → Poly R)
    (hφ : ∀ U, (φ U).part R.quiet = 0) (V : Config G (H.S.side j n)) :
    let D := fun U => ((fine).eval U : ℂ) • Poly.pass (φ U)
    (Actual.Push S (fine).beta D V).part R.quiet = ((coarse).eval V : ℂ) ∧
      0 < (coarse).eval V := by
  intro D
  apply measured_quiet H hs step D _ V
  intro U
  change (((fine).eval U : ℂ) • Poly.pass (φ U)).part R.quiet = _
  rw [Poly.part_smul, Poly.pass_part _ (hφ U), mul_one]

/-- Original inverse-square-root physical coupling. -/
abbrev measuredCoupling (β : ℝ) := (Real.sqrt β)⁻¹

theorem physical_temperature :
    temperature (measuredCoupling (fine).beta) = (fine).beta := by
  have h := SectorNext.Vacuum.beta_positive H hs N n (j+1) step
  rw [temperature, measuredCoupling, inv_pow, inv_inv, Real.sq_sqrt h.le]

end YM.Integration.FVA1Physical.OriginalMixedWilson
