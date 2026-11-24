import YM.Integration.WilsonPositionOriginalDressedQJointMoment

/-! The actual one-step panel of the Original Q school on the enrolled
run, with the physical kinetic coordinate and the exact prior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQMeasuredPane
open Lattice Wilson RG Cells Marker OPE.Therm
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato QuadraticLocal
open Mentor MintClock AllOrder AllOrder.Transit AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset
open scoped Classical
variable {G:Gauge}(R:Run G)

theorem panel (i p:ℕ):
    Pane.panel R.alloy i (R.alloy.B.a.S.oneStep i p).exact_size =
      R.family.path.levels.clock.op i p:=by
  rfl

end YM.Integration.WilsonPositionOriginalDressedQMeasuredPane
