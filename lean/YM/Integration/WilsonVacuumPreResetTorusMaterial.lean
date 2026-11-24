import YM.Integration.WilsonVacuumPreResetTorusKernel
import YM.Integration.PhysicalWilsonPeriodizedMaterial
import YM.Integration.ManuscriptQLocalStationaryGeometry

/-! The finite old-field FK operator against the periodization of the actual
original directed Gaussian with the authentic rotation average and determinant. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusMaterial
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



open WilsonVacuumPreResetTorusRegister Comparison.RG02.Order
open Next.SectorChange PhysicalNext.Repeat Marker Exterior

def physicalAngle (n:Side)(z:rule (Coarse G) n):fieldDir G n 1:=
  tint G (Exterior.Body 1 n) (exteriorL G n z)

theorem charged {N b j k:ℕ}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (path:PlanV.Path r R.alloy Q (Burn.horizon k) N b π Γ)(early:b≤j)(live:j<N):
    Legal (AllOrder.Floe.Step.tape (Burn.horizon k+2)) (π (j+1)):=by
  constructor
  · intro a mem
    exact ⟨_,_,(r.shape _).pos (R.alloy.B.a.clock.J (j+1)) a,
      (path.1 (j+1) (by omega) (by omega) a mem).pay⟩
  · intro a mem
    exact (path.1 (j+1) (by omega) (by omega) a mem).symm

variable {I:Type} [Fintype I] [DecidableEq I] {J:Marker.Census I}

theorem measured {N b j k:ℕ}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (path:PlanV.Path r R.alloy Q (Burn.horizon k) N b π Γ)(early:b≤j)(live:j<N)
    (per:ℕ)(w:Bulk.Colors J G (R.family.side (j+1) per))(hw:Bulk.Well w)
    (Y:Forest (R.alloy.B.a.clock.op j per).ratio)(tag:(R.alloy.B.a.clock.op j per).Choices)
    (z:rule (Coarse G) (R.family.side j per)){t:ℕ}(valid:t≤Burn.horizon k+2):
    let K:=(RunFormalChain.fromRun R).step N j per live
    let data:=QuadraticLocal.Fk.grant (π (j+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2)) w
    let angle:=physicalAngle (R.family.side j per) z
    finite R N j k π t (R.family.side j per) z =
      Comparison.RG02.Laplace.detail
        (logVac (PhysicalWilsonPeriodizedMaterial.reference R N j per live angle data (Burn.horizon k+2)))
        J.quiet t + if t=0 then Symmetry.price K Y tag angle else 0:=by
  intro K data angle
  let seat:=ActualRunSpring.selected R N per j live
  let H:=seat.spring.H.houses seat.point
  have patch:(R.alloy.B.a.clock.op j per).patch=
      Mural.sheet R.metals.p R.rolls (R.alloy.B.a.clock.adm (j+1)):=H.laws.data.funds.patch rfl rfl
  have kra:(R.alloy.B.a.clock.op j per).kernel=R.metals.p.kernel:=R.alloy.B.valid.kernel
  let book:=RunFormalChain.fromRun R
  have clip:(R.family.path.rep N per (j+1)).clip=(R.metals.p.profile (R.alloy.B.a.clock.J (j+1))).clip:=by
    exact (book.clips N per (j+1) live).trans (congrArg RG.Stage.clip (params_eq R.alloy.B.valid (j+1)))
  have kinetic:(R.family.path.rep N per (j+1)).path=R.alloy.B.kin.path N (j+1):=
    book.selected N per (j+1) live
  have held:=WilsonVacuumPreResetTorusKernel.measured R path early live patch kra
    (ManuscriptQLocalStationaryGeometry.larger R N j per live) w Y tag z valid
  dsimp only at held
  rw [←clip,←kinetic] at held
  refine (held K).symm.trans ?_
  change Comparison.RG02.Laplace.detail (logVac (Bulk.Fk K Y tag data angle (Burn.horizon k+2)))
    J.quiet t+_=_
  have full:Bulk.Well data:=(QuadraticLocal.Fk.well _ _ (charged R path early live) w hw).1
  rw [PhysicalWilsonPeriodizedMaterial.original R N j per live angle data (Burn.horizon k+2) Y tag full]
  rfl

theorem original {N b j k:ℕ}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (path:PlanV.Path r R.alloy Q (Burn.horizon k) N b π Γ)(early:b≤j)(live:j<N)
    (per:ℕ)(Y:Forest (R.alloy.B.a.clock.op j per).ratio)(tag:(R.alloy.B.a.clock.op j per).Choices)
    (z:rule (Coarse G) (R.family.side j per)){t:ℕ}(valid:t≤Burn.horizon k+2):
    let w:=Bulk.Colors.noHole G (R.family.side (j+1) per) unmarked
    let data:=QuadraticLocal.Fk.grant (π (j+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2)) w
    let angle:=physicalAngle (R.family.side j per) z
    finite R N j k π t (R.family.side j per) z =
      Comparison.RG02.Laplace.detail
        (logVac (PhysicalWilsonPeriodizedMaterial.reference R N j per live angle data (Burn.horizon k+2)))
        unmarked.quiet t + if t=0 then
          Symmetry.price ((RunFormalChain.fromRun R).step N j per live) Y tag angle else 0:=
  measured R path early live per _ (Bulk.Colors.no_hole G _ unmarked).1 Y tag z valid

end YM.Integration.WilsonVacuumPreResetTorusMaterial
