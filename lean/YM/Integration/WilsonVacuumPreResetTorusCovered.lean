import YM.Integration.FVA1Physical.MixedResets.VacuumCover
import YM.Integration.WilsonMovingMentorItinerary

/-! Every interim card on the chosen unmarked history, including cards with
nonbare incoming rows, reads its own published coefficients on all physical repeats. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusCovered
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
open Kinetic.Port PhysicalNext.Repeat.Legato FVA1Physical.MixedResets
open RG.Supply Push.PriceCompiler AbsoluteSums ConnectedActivityE6
open PhysicalNext PhysicalNext.Repeat ThroughLaunch Pane
open Bid Org Further.PhysicalPeriodLimitF933 Shingle Aero Comparison.RG02

variable {G:Gauge}(R:Run G)
variable {r:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
variable {Q:r.Tab R.rolls}
set_option quotPrecheck false
local notation "V" => R.alloy.B.a

def Report {N j k:ℕ} (π:ℕ → Layout G) (C:WilsonMovingMentorItinerary.CardAt R r k j)
    (rank:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J j) : Prop :=
  let I:=PlanV.litP r R.alloy Q rank C
  let P:=Mural.sheet R.metals.p R.rolls (R.alloy.B.a.clock.adm (j+1))
  let L:=R.alloy.B.kin.path N (j+1)
  let clip:=(R.metals.p.profile (R.alloy.B.a.clock.J (j+1))).clip
  let T:=AllOrder.Floe.Step.tape (Burn.horizon k+2)
  let F:=vacuumBill P R.metals.p.kernel R.metals.O L clip (π (j+1)) T (Burn.horizon k+2)
  ∀t:ℕ,t ≤ Burn.horizon k+2 → ∀c:Side,∀z:rule (Coarse G) c,
    (vista I.presence C t c z : ℂ)=coverAction P R.metals.p.kernel R.metals.O L clip
      (π (j+1)) T (Burn.horizon k+2) t z ∧
    ∀(s:ℕ → Side)(w:ℕ → ℕ)(window:∀i,Macrame.Window c (s i) (w i)),
      (∀i,0<w i) → Tendsto (fun i=>(s i).val) atTop atTop →
        Tendsto (fun i=>tileAt (F t) (window i) z) atTop (𝓝 (vista I.presence C t c z:ℂ))

theorem measured {k b N:ℕ} {π:ℕ → Layout G} {Γ:ℕ → Pace.Coin}
    (path:PlanV.Path r R.alloy Q (Burn.horizon k) N b π Γ) {j:ℕ}(early:b ≤ j)(live:j<N) :
    ∃ (C:WilsonMovingMentorItinerary.CardAt R r k j) (rank:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J j),
      PlanV.Journey r R.alloy (m:=j) (N:=N) C ∧ π (j+1)=C.extra ∧
      π j=(PlanV.litP r R.alloy Q rank C).laid C ∧ Γ j=(PlanV.litP r R.alloy Q rank C).issue C ∧
      Report R (Q:=Q) (N:=N) π C rank:=by
  obtain ⟨C,rank,moves,upper,lower,coin⟩:=path.2.2 j early live
  refine ⟨C,rank,moves,upper,lower,coin,?_⟩
  dsimp only [Report]
  intro t valid c z
  simpa only [moves.books.north,←upper] using
    (cover_vacuum_law (assets:=R.metals) (PlanV.litP r R.alloy Q rank C) C z valid)

end YM.Integration.WilsonVacuumPreResetTorusCovered
