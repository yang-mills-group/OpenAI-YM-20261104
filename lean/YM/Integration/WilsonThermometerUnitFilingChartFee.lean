import YM.Integration.WilsonThermometerUnitFilingFieldRange
import YM.Integration.WilsonMeasuredCourseQuietSlots

/-! The cost of the native raw representative has a fixed pole determined by its physical grade. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingChartFee
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonThermometerUnitFilingFieldRange
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {N per m k:ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
  (Ψ:∀j,RG.Rep G (R.family.side j per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)

include π Γ course in
theorem original (d:ℕ) {j:ℕ} (floor:m ≤ j) (top:j ≤ N):
    cost G d (Ψ j).p.threshold+5 ≤ (6+basisCost G d)*R.family.path.levels.clock.hatBeta j^d:=by
  let A:=R.family.path.levels
  let B:=A.clock.hatBeta j
  have one:1 ≤ B:=(A.fits.delayed j).le
  have positive:0 ≤ B:=zero_le_one.trans one
  have monitor:1 ≤ A.clock.monitor j:=Real.one_le_exp (sq_nonneg _)
  have root:Real.sqrt B ≤ B:=by
    have fromOne:=Real.sqrt_le_sqrt one
    rw [Real.sqrt_one] at fromOne
    nlinarith only [mul_le_mul_of_nonneg_left fromOne (Real.sqrt_nonneg B),Real.sq_sqrt positive]
  have upper:(A.clock.threshold j)⁻¹ ≤ B:=by
    change ((_ : ℝ)⁻¹ * A.clock.monitor j)⁻¹ ≤ B
    rw [mul_inv_rev,inv_inv]
    exact (mul_le_mul_of_nonneg_right ((inv_le_one₀ (zero_lt_one.trans_le monitor)).mpr monitor)
      (Real.sqrt_nonneg _)).trans ((one_mul _).le.trans root)
  have point:((R.family.path.rep N per j).p)=(Ψ j).p:=
    (WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course floor top).1
  have placed:(Ψ j).p.threshold=A.clock.threshold j:=by
    change (Ψ j).p.threshold=(A.budget j).threshold
    have receive:(Ψ j).p=A.budget j:=point.symm.trans (R.makes.wilson.represents N per j top).vac
    exact congrArg (fun w=>w.threshold) receive
  have weight:(max 1 (Ψ j).p.threshold⁻¹)^d ≤ B^d:=
    pow_le_pow_left₀ (zero_le_one.trans (le_max_left ..)) (max_le one (placed ▸ upper)) _
  have basis:0 ≤ basisCost G d:=zero_le_one.trans (Next.Foundations.full_value_bound (G:=G) d).choose_spec.1
  have bill:=mul_le_mul_of_nonneg_left weight basis
  have rebate:1 ≤ B^d:=one_le_pow₀ one
  change 1+basisCost G d*(max 1 (Ψ j).p.threshold⁻¹)^d+5 ≤ (6+basisCost G d)*B^d
  linarith

end YM.Integration.WilsonThermometerUnitFilingChartFee
