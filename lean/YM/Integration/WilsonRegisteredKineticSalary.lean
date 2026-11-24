import YM.Integration.WilsonRegisteredKineticLeaf
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Geometry

/-! Absolute price of the complete ordered kinetic roster at its physical
root. Half the original path exponent remains on the numerical charge. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonRegisteredKineticSalary
open Function Finset Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson MeasureTheory
open ConnectedActivityE6 Precision Exterior Shell Channel Next.Scheduling WilsonStartup
open Work.E03 RGLocalTaylor RGLocalTaylor.Insert PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato AnalyticBridge.VerifiedReset RG01Estimate
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus Progress.DirectedRecipe
open scoped Topology Classical BigOperators
open Push.AbsoluteSums Extra.Iteration Next.Scheduling AnalyticBridge.VerifiedReset.Geo WilsonRegisteredKineticLeaf

variable {G : Gauge}

def factor (p : BudgetPoint) (a : ℝ) := WardBin.Wheels.tariff p * |a| * p.threshold^2

theorem counted (K : PathData G) (p : BudgetPoint) {B : Clip} {σ C Λ : ℝ}
    (bounds : K.Bounds B σ C Λ) (a : ℝ) :
    SumBudget (fun d : Low => income K B p d a * Real.exp ((σ/2)*d.length K))
      (factor p a * (lowFee G p σ * lowerSize B C)) := by
  have fp : 0 ≤ factor p a := mul_nonneg
    (mul_nonneg (WardBin.Wheels.tariff_positive p).le (abs_nonneg a)) (sq_nonneg _)
  apply Cost.mono (Cost.scale (low_budget G p K bounds) _ fp)
  · intro d
    have h := add_nonneg (faceCost_nonneg G p) (row_nonneg G p (d.length K))
    exact mul_nonneg (mul_nonneg (WardBin.Wheels.tariff_positive p).le
      (mul_nonneg (abs_nonneg _) (mul_nonneg h (sq_nonneg _)))) (Real.exp_pos _).le
  · intro d
    have h : faceCost G p + rowCost G p (d.length K) ≤ lowCost G p (d.length K) := by
      unfold lowCost
      exact le_add_of_nonneg_left (mul_nonneg (by norm_num) (pair_nonneg _ _))
    calc
      _ = factor p a * (|d.mark K B| * (faceCost G p + rowCost G p (d.length K)) *
          Real.exp ((σ/2)*d.length K)) := by unfold WilsonRegisteredKineticLeaf.income factor; rw [abs_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h (abs_nonneg _)) (Real.exp_pos _).le) fp

theorem purchased (R : Run G) {N k : ℕ} (hk : k ≤ N) (per : ℕ)
    (p : BudgetPoint) (a : ℝ) :
    let D := R.family.path.levels.params k
    let K := (R.family.path.rep N per k).path
    SumBudget (fun d : Low => income K D.clip p d a * Real.exp ((D.width/2)*d.length K))
      (factor p a * (lowFee G p D.width * lowerSize D.clip D.paths)) := by
  have law : R.family.path.Conv N per k := R.makes.wilson.represents N per k hk
  apply counted (Λ:=R.family.path.levels.clock.loopCap k)
  rw [←law.clip]
  exact law.good.paths

end YM.Integration.WilsonRegisteredKineticSalary
