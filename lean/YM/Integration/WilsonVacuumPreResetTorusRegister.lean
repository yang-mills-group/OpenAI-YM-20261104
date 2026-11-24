import YM.Integration.WilsonVacuumPreResetTorusCovered
import YM.Integration.WilsonVacuumPreResetTorusRepriced

/-! Every interim card on the chosen unmarked history, including cards with
nonbare incoming rows, reads its own published coefficients on all physical repeats. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusRegister
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

open WilsonVacuumPreResetTorusRepriced

def earlier (N j k:ℕ)(π:ℕ → Layout G)(t:ℕ){c:Side}(z:rule (Coarse G) c):ℂ:=
  coverAction (Mural.sheet R.metals.p R.rolls (R.alloy.B.a.clock.adm (j+1))) R.metals.p.kernel
    R.metals.O (R.alloy.B.kin.path N (j+1)) (R.metals.p.profile (R.alloy.B.a.clock.J (j+1))).clip
    (π (j+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2)) (Burn.horizon k+2) t z

def finite (N j k:ℕ)(π:ℕ → Layout G)(t:ℕ):=
  vacuumBill (Mural.sheet R.metals.p R.rolls (R.alloy.B.a.clock.adm (j+1))) R.metals.p.kernel
    R.metals.O (R.alloy.B.kin.path N (j+1)) (R.metals.p.profile (R.alloy.B.a.clock.J (j+1))).clip
    (π (j+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2)) (Burn.horizon k+2) t

theorem original {k b N:ℕ}{π:ℕ → Layout G}{Γ:ℕ → Coin}
    (path:PlanV.Path r R.alloy Q (Burn.horizon k) N b π Γ)
    (j:ℕ)(early:b≤j)(live:j<N){t:ℕ}(valid:t≤Burn.horizon k+2)
    (c:Side)(z w:rule (Coarse G) c):
    let filed:=Reading R N j k π Γ t c
    ((filed z-filed w:ℝ):ℂ)=earlier R N j k π t w-earlier R N j k π t z ∧
    ∀(s:ℕ → Side)(d:ℕ → ℕ)(window:∀i,Macrame.Window c (s i) (d i)),
      (∀i,0<d i) → Tendsto (fun i=>(s i).val) atTop atTop →
      Tendsto (fun i=>tileAt (finite R N j k π t) (window i) w-
        tileAt (finite R N j k π t) (window i) z) atTop (𝓝 ((filed z-filed w:ℝ):ℂ)):=by
  intro filed
  obtain ⟨C,rank,moves,upper,lower,coin,report⟩:=
    WilsonVacuumPreResetTorusCovered.measured R path early live
  let panel:=vista (PlanV.litP r R.alloy Q rank C).presence C t c
  have charged:filed z-filed w = -(panel z-panel w):=
    reported R π Γ C rank moves lower coin (by omega) c z w
  have reg:((filed z-filed w:ℝ):ℂ)=(panel w:ℂ)-(panel z:ℂ):=by
    rw [← Complex.ofReal_sub]
    exact congrArg Complex.ofReal (by linarith only [charged])
  have hz:=report t valid c z
  have hw:=report t valid c w
  constructor
  · exact reg.trans (congrArg₂ (·-·) hw.1 hz.1)
  · intro s d window positive grows
    rw [reg]
    exact (hw.2 s d window positive grows).sub (hz.2 s d window positive grows)

end YM.Integration.WilsonVacuumPreResetTorusRegister
