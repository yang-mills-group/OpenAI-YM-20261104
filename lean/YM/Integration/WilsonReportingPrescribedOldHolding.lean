import YM.Integration.ManuscriptQLocalMarkedHeightRun

/-! Recover the entire old signed mark on the actual nonbare angular carrier. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldHolding

open Lattice Wilson RG Marker Precision LocalComparison LocalComparison.Global
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open ComparisonDensity.Address

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
  (R : Run G) {J : Request V} (A : NumericSchedule R.family J)
  (d : LocalFormal.Datum R.family Γ) (F : AnalyticInput J A d)
  {η : ℝ} (I : FullPreparedInputAt F η)

local notation "g₁" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "inlet" => QLocalInheritedPhysicalInlet.rep I
local notation "old" => ManuscriptQLocalVacuumFamily.source (inlet) F.layers g₁ 1

abbrev retained (t : TestSpace J.tests) (U : Config G (R.family.side (d.level+1) d.period)) :=
  ((QLocalInheritedRegularSlots.marked (old) (ManuscriptQLocalVacuumFamily.carry
    (inlet) F.layers g₁ 1 (QLocalInheritedPhysicalInlet.carried I I.prepared.remainder))).leaf t).density U

/-- Only the registered scalar calibration and the invertible source exponential
are removed. The complete old hard gas stays in the measured density. -/
theorem original (hi : Retained.NativeIntake I) (t : TestSpace J.tests)
    (U : Config G (R.family.side (d.level+1) d.period)) :
    retained R A d F I t U =
      (Real.exp (I.calibration.amount U) : ℂ) •
        (Poly.pass (-(F.packets.read t g₁ U)) * (I.input.leaf t).density U) := by
  rw [ManuscriptQLocalMarkedHeightRun.material R A d F I hi t U, mul_smul_comm,
    ← mul_assoc, Next.Rank.Exponential.pass_neg _ (F.packets.quiet_read t g₁ U),
    one_mul, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, Complex.ofReal_one, one_smul]

end YM.Integration.WilsonReportingPrescribedOldHolding
