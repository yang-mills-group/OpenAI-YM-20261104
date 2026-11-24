import YM.Integration.WilsonMovingMentorItinerary

/-! The actual old physical run's newly laid vacuum tape and reset coin on
each dated torus. Every coefficient of its negative sum with the submitted
unreset panel is constant in the complete coarse field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusRepriced
open AllOrder AllOrder.Floe AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Classical Topology BigOperators

open Primitives.TwoWave Primitives.TwoWave.RealSlice
open Kinetic.Port PhysicalNext.Repeat.Legato

variable {G:Gauge}(R:Run G)
variable {r:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
variable {Q:r.Tab R.rolls}
set_option quotPrecheck false
local notation "V" => R.alloy.B.a

def Reading (N j k:ℕ) (π:ℕ → Layout G) (Γ:ℕ → Coin) (t:ℕ) (c:Side) :=
  Pace.grouping (Γ j) (π j) (Age.scope (Burn.horizon k+2))
    (R.metals.p.profile (R.alloy.B.a.clock.J j)).clip (R.alloy.B.kin.path N j) t c

theorem reported {N j k:ℕ} (π:ℕ → Layout G) (Γ:ℕ → Coin)
    (C:WilsonMovingMentorItinerary.CardAt R r k j)
    (rank:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J j)(moves:PlanV.Journey r R.alloy (N:=N) C)
    (lower:π j=(PlanV.litP r R.alloy Q rank C).laid C)
    (coin:Γ j=(PlanV.litP r R.alloy Q rank C).issue C)
    {t:ℕ}(valid:t<Burn.horizon k+3)(c:Side)(z w:rule (Coarse G) c):
    let panel:=vista (PlanV.litP r R.alloy Q rank C).presence C t c
    let filed:=Reading R N j k π Γ t c
    filed z-filed w=-(panel z-panel w):=by
  intro panel filed
  let I:=PlanV.litP r R.alloy Q rank C
  have bill:=I.sustenance.calls C c t valid z w
  change 0-panel z-Pace.grouping (I.issue C) (I.laid C) (Age.scope (Burn.horizon k+2))
    (R.metals.p.profile (R.alloy.B.a.clock.J j)).clip C.self.south t c z =
    0-panel w-Pace.grouping (I.issue C) (I.laid C) (Age.scope (Burn.horizon k+2))
    (R.metals.p.profile (R.alloy.B.a.clock.J j)).clip C.self.south t c w at bill
  rw [moves.books.south, ←lower, ←coin] at bill
  change Reading R N j k π Γ t c z-Reading R N j k π Γ t c w=_
  unfold Reading
  linarith only [bill]

end YM.Integration.WilsonVacuumPreResetTorusRepriced
