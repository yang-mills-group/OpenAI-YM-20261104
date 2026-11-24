import YM.Integration.WilsonVacuumPreResetTorusPhysicalPeriod
import YM.WilsonCoeffUV.Reclosure.CurlTorus
import YM.WilsonCoeffUV.Vacuum.Recursion

/-! The independently filed finite pre-reset tensor and the periodization
of its cover limit on the same physical growing periods, at every old date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusSeason
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
variable {G:Gauge}(R:Run G)

theorem grows (j:ℕ):Tendsto (R.family.side j) atTop atTop:=by
  refine tendsto_atTop.2 fun n=>?_
  filter_upwards [R.family.S.period_strict.tendsto_atTop.eventually_ge_atTop n.val] with p hp
  exact hp.trans (Nat.le_mul_of_pos_right _ (R.family.S.denominator j).property)

def source (N j i q:ℕ)(n:Side):=
  let A:=R.family.path.levels
  unripe A R.metals.O N j (story A R.metals.O N (j+1)).1 n i q

def output (N j i q:ℕ):=
  freshet R.family.path.levels R.metals.O N j i q

theorem original (simple:G.Simple){N j:ℕ}(older:j<N)(i q:ℕ)
    (x:Fin q→YForest G):
    Tendsto (fun per=>let n:=R.family.side j per
      dilute (source R N j i q) n (foldUnder n ∘ x)) atTop (𝓝 (output R N j i q x)):=by
  have proper:LocalRatio R.metals.O:=(RunFormalChain.fromRun R).receipt
  have price:=(perch R.family.path.levels R.metals.O simple proper older).growth i q
  exact (price.point x).comp (grows R j)

theorem corrected (simple:G.Simple){N j:ℕ}(older:j<N)(i l:ℕ)
    (x:Fin (l+1)→YForest G):
    Tendsto (fun per=>let n:=R.family.side j per
      source R N j i (l+1) n (foldUnder n ∘ x)-
      lagoon (output R N j i (l+1)) n (foldUnder n ∘ x)) atTop (𝓝 0):=by
  have proper:LocalRatio R.metals.O:=(RunFormalChain.fromRun R).receipt
  have price:=(perch R.family.path.levels R.metals.O simple proper older).growth i (l+1)
  obtain ⟨σ,A,warm,cost⟩:=price.cover
  have sheet:=(lagoon_yields cost warm price.road).point x
  have same:=(original R simple older i (l+1) x).sub (sheet.comp (grows R j))
  simpa only [Function.comp_apply,dilute,Nat.succ_ne_zero,↓reduceIte,output,freshet,actionW,sub_self] using same

end YM.Integration.WilsonVacuumPreResetTorusSeason
