import YM.Integration.WilsonCenteredStampedKeeper
import YM.Integration.WilsonMovingMentorConcourseRows

/-! The complete marked receiving course already carries the literal
outgoing hard layout needed for the signed physical capture. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCourseKeeper
open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Org Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit AllOrder.Transit.WheelP Planned.GuardedAtom
open AnalyticBridge VerifiedReset
open scoped Classical Topology

theorem original {G : Gauge} (R : Run G) {m N per k : ℕ}
    {π : ℕ → Layout G} {Γ : ℕ → Pace.Coin} {H : (i : ℕ) → Rep G (R.alloy.B.a.S.side i per)}
    (course : Concourse R.alloy R.kit R.T π Γ m N per k H) (i : ℕ) (early : m ≤ i)
    (live : i < N) : Nonempty (Guard.Keeper (H i).p (H i).activities) := by
  obtain ⟨_,_,⟨walk⟩⟩:=WilsonMovingMentorConcourseRows.guide R course i early live
  exact ⟨WilsonCenteredStampedKeeper.original (H i) walk.second⟩

end YM.Integration.WilsonCenteredCourseKeeper
