import YM.Integration.WilsonVacuumPreResetTorusRegister

/-! The genuine finite-period unmarked Gaussian action prior to its cover
limit, on every physical forest and covariance of the enrolled step. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusKernel
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


open WilsonVacuumPreResetTorusRegister

theorem measured {N b j k:ℕ}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (path:PlanV.Path r R.alloy Q (Burn.horizon k) N b π Γ)(early:b≤j)(live:j<N)
    {I:Type}[Fintype I][DecidableEq I]{J:Marker.Census I}{n f:Side}{S:StepData n f}
    (patch:S.patch=Mural.sheet R.metals.p R.rolls (R.alloy.B.a.clock.adm (j+1)))
    (kernel:S.kernel=R.metals.p.kernel)(big:Larger (G:=G) S)
    (w:Bulk.Colors J G f)(Y:Forest S.ratio)(tag:S.Choices)(z:rule (Coarse G) n)
    {t:ℕ}(valid:t≤Burn.horizon k+2):
    let C:=(R.metals.p.profile (R.alloy.B.a.clock.J (j+1))).clip
    let L:=R.alloy.B.kin.path N (j+1)
    ∀g:Bulk.Kernel S C L R.metals.O,
      vacuumFK R.metals.O L C (π (j+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        (Burn.horizon k+2) t w g Y tag z = finite R N j k π t n z:=by
  obtain ⟨card,rank,moves,upper,lower,coin⟩:=path.2.2 j early live
  dsimp only
  unfold finite
  rw [←moves.books.north,upper]
  intro g
  exact action_identifies (PlanV.litP r R.alloy Q rank card) card patch kernel big g w Y tag z valid

end YM.Integration.WilsonVacuumPreResetTorusKernel
