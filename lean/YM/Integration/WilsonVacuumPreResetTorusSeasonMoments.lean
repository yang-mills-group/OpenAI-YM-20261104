import YM.Integration.WilsonVacuumPreResetTorusMoment
import YM.Integration.WilsonVacuumPreResetTorusSeasonFiled

/-! Rooted convergence on the physical sequence against arbitrary signed,
period-dependent probes of polynomial growth on the original leg tuple. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusSeasonMoments
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
variable {G:Gauge}(R:Run G)

def mismatch (N j i l:ℕ):raw (Hooks G) ℝ (l+1):=
  source R N j i (l+1)-lagoon (output R N j i (l+1))

theorem ranked (simple:G.Simple){N j:ℕ}(older:j<N)(i l d:ℕ)(x:YForest G):
    Tendsto (fun per=>∑y,term (mismatch R N j i l) d x (R.family.side j per) y) atTop (𝓝 0):=by
  have proper:LocalRatio R.metals.O:=(RunFormalChain.fromRun R).receipt
  have tracked:Yields (source R N j i (l+1)) (output R N j i (l+1)):=
    (perch R.family.path.levels R.metals.O simple proper older).growth i (l+1)
  obtain ⟨σ,A,warm,bill⟩:=tracked.cover
  have same:Yields (mismatch R N j i l) 0:=by
    simpa only [mismatch,sub_self] using tracked.sub (lagoon_yields bill warm tracked.road)
  exact (WilsonVacuumPreResetTorusMoment.original _ same x d).comp (grows R j)

theorem tested (simple:G.Simple){N j:ℕ}(older:j<N)(i l d:ℕ)(x:YForest G)
    (H:∀per,dock (Site (R.family.side j per)) (Hooks G) l→ℂ)
    (bound:∀p y, ‖H p y‖≤(1+soar (tor (R.family.side j p))
      (Fin.cons (foldUnder (R.family.side j p) x) y):ℝ)^d):
    Tendsto (fun per=>let n:=R.family.side j per
      ∑y,mismatch R N j i l n (Fin.cons (foldUnder n x) y) • H per y) atTop (𝓝 0):=by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _=>norm_nonneg _) (fun p=>?_) (ranked R simple older i l d x)
  refine (norm_sum_le _ _).trans (sum_le_sum fun y _=>?_)
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (bound p y) (norm_nonneg _)).trans_eq (mul_comm ..)

end YM.Integration.WilsonVacuumPreResetTorusSeasonMoments
