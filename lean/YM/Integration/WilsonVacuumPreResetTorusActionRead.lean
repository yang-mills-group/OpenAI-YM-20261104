import YM.Integration.WilsonVacuumPreResetTorusSeasonPainting
import YM.Integration.WilsonVacuumPreResetTorusGrade
import YM.Integration.WilsonVacuumPreResetTorusSeasonFiled
import YM.Integration.WilsonLimitConstruction.FundedSpringPeriodGerm

/-! The entire pre-reset scalar difference of the independent step on the
physical period sequence equals the registered earlier corrected action on its cover. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusActionRead
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

open WilsonVacuumPreResetTorusRegister WilsonVacuumPreResetTorusMaterial
open Comparison.RG02.Order Next.SectorChange Marker Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetTorusSeason WilsonVacuumPreResetTorusMoment
open WilsonVacuumPreResetTorusSeasonMoments WilsonVacuumPreResetTorusPhysicalPeriod
open Function Filter Finset Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree MeasureTheory
open ConnectedActivityE6 ConnectedActivityE6.Coat
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure
open Bloch Laurent RG.Supply Extra.Histories GapsLocal.Renew
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Opera
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Physical WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Bloom WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonCoeffUV.Fk Next.Foundations WilsonLimitConstruction WilsonStartup PowerSeries
open scoped Topology BigOperators Classical
open WilsonVacuumPreResetTorusSeason
open WilsonVacuumPreResetTorusSeasonPainting WilsonVacuumPreResetTorusGrade
variable {G:Gauge}(R:Run G)

def originalAction (N j:ℕ)(n:Side):PChart G n:=
  let A:=R.family.path.levels
  unripe A R.metals.O N j (story A R.metals.O N (j+1)).1 n

def corrected (N j:ℕ)(Z:SeriesA G)(n:Side):PChart G n:=
  let A:=R.family.path.levels
  Blue.mix (pace (pitch A R.metals.O N j))
    (front (R.alloy.B.kin.path N j) (A.params j).clip n+sands Z n)

def sampleDiff (N j t per:ℕ)(z w:rule (Coarse G) (base R.family.S j)):ℂ:=
  let Y:=originalAction R N j (R.family.side j per)
  let win:=window R.family.S j per
  (evaluated Y t (convey win z)-evaluated Y t (convey win w):ℝ)

def correctedDiff (N j t:ℕ)(Z:SeriesA G)(z w:rule (Coarse G) (base R.family.S j)):ℂ:=
  let Y:=corrected R N j Z (base R.family.S j)
  (evaluated Y t z-evaluated Y t w:ℝ)

theorem original (simple:G.Simple){N j t:ℕ}(older:j<N)(Z:SeriesA G)
    (filed:∀l,corrected R N j Z (base R.family.S j) t (l+1)=
      lagoon (output R N j t (l+1)) (base R.family.S j))
    (z w:rule (Coarse G) (base R.family.S j)):
    Tendsto (fun per=>(copies R.family.S per:ℝ)⁻¹ • sampleDiff R N j t per z w) atTop
      (𝓝 (correctedDiff R N j t Z z w)):=by
  let c:=base R.family.S j
  let n:=R.family.side j
  let M:=copies R.family.S
  let F:=corrected R N j Z c
  have bound:shellK 2 F:=mix_length (FundedSpringPeriodGerm.grade c
    (R.family.path.levels.params j).clip (R.alloy.B.kin.path N j) Z)
  have before (per:ℕ):sampleDiff R N j t per z w=
      ∑l∈Finset.range (t+2),(WilsonVacuumPreResetTorusSeasonPainting.sample R N j t l per z-WilsonVacuumPreResetTorusSeasonPainting.sample R N j t l per w):=by
    let win:=window R.family.S j per
    have here:=WilsonVacuumPreResetTorusGrade.positive (originalAction R N j (n per))
      (WilsonVacuumPreResetTorusGrade.original R simple older (n per)) t (convey win z) (convey win w)
    simpa only [sampleDiff,WilsonVacuumPreResetTorusSeasonPainting.sample,WilsonVacuumPreResetTorusSeason.source,originalAction,n,win,Complex.ofReal_sum,Complex.ofReal_sub] using congrArg Complex.ofReal here
  have after:correctedDiff R N j t Z z w=
      ∑l∈Finset.range (t+2),(record R N j t l z-record R N j t l w):=by
    have here:=WilsonVacuumPreResetTorusGrade.positive F bound t z w
    have sold (l:ℕ):F t (l+1)=lagoon (output R N j t (l+1)) c:=filed l
    simpa only [correctedDiff,record,Complex.ofReal_sum,Complex.ofReal_sub,sold] using congrArg Complex.ofReal here
  have each (l:ℕ):Tendsto (fun p=>(M p:ℝ)⁻¹ • (WilsonVacuumPreResetTorusSeasonPainting.sample R N j t l p z-WilsonVacuumPreResetTorusSeasonPainting.sample R N j t l p w)) atTop
      (𝓝 (record R N j t l z-record R N j t l w)):=by
    simpa only [smul_sub] using (WilsonVacuumPreResetTorusSeasonPainting.original R simple older t l z).sub
      (WilsonVacuumPreResetTorusSeasonPainting.original R simple older t l w)
  rw [after]
  simpa only [before,Finset.smul_sum] using tendsto_finsetSum (Finset.range (t+2)) (fun l _=>each l)

end YM.Integration.WilsonVacuumPreResetTorusActionRead
