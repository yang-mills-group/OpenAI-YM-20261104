import YM.Integration.WilsonPhysicalStationMixedWickMeasured
import YM.Integration.WilsonPhysicalStationLowerReceiver

/-! Assemble the right enrolled fields at one actual relative placement and
its physical radius. Both contributions are linear in the same input. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickRespondents
open Function Filter Finset Lattice RG Wilson Labels Source Cells Extraction Table Spec OPE
open PhysMS Maxwell.Free PhysicalNext.Repeat.Legato Further.CorrectedLift
open WilsonOriginalBlissMixedGram (grades)
open WilsonPhysicalStationLowerReceiver (pair ear evaluated)
open WilsonPhysicalStationMixedWickTest (reference)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(U:tower S)
    {l r:ℕ}(measured prepared:Points 2)(x:(standard R.family).Field l)
local notation "C₀" => standard R.family

def native:(C₀).Field r→ₗ[ℂ]ℂ:=
  ((S.classMoment S (grades l r) measured).toLinearMap (pair R (U l x) (0:S.Field r)) (1:Fin 2)).comp
    (U r).toLinearMap

def independent:(C₀).Field r→ₗ[ℂ]ℂ:=
  ((C₀).classMoment (C₀) (grades l r) prepared).toLinearMap
    (WilsonPhysicalStationMixedWickTest.fields R.family (ladder R.family l x) (0:(C₀).Field r)) (1:Fin 2)

def balance:(C₀).Field r→ₗ[ℂ]ℂ:=native R U measured x-independent R prepared x

theorem actual (z:(C₀).Field r):
    native R U measured x z=ear R (S:=S) measured (U r z) (U l x):=by
  rw [evaluated]
  change S.classMoment S (grades l r) measured (Function.update (pair R (U l x) (0:S.Field r)) 1 (U r z))=_
  congr 1
  funext i
  fin_cases i <;> simp [pair,Function.update]

theorem reported (z:(C₀).Field r):
    independent R prepared x z=reference R.family (ladder R.family l x) z prepared:=by
  change (C₀).classMoment (C₀) (grades l r) prepared (Function.update
      (WilsonPhysicalStationMixedWickTest.fields R.family (ladder R.family l x) (0:(C₀).Field r)) 1 z)=_
  apply congrArg ((C₀).classMoment (C₀) (grades l r) prepared)
  funext i
  fin_cases i <;> simp [WilsonPhysicalStationMixedWickTest.fields,Function.update]

theorem incurred (z:(C₀).Field r):
    balance R U measured prepared x z=ear R (S:=S) measured (U r z) (U l x)-
      reference R.family (ladder R.family l x) z prepared:=by
  change native R U measured x z-independent R prepared x z=_
  rw [actual,reported]

theorem priced {I:Type*}[Fintype I](z:(C₀).Field r)(peers:I→(C₀).Field r)(μ:I→ℂ)
    (votes:z=∑i,μ i • peers i)(scale:ℝ)(hs:0 ≤ scale)(cost:I→ℝ)
    (seated:∀i,μ i≠0 → scale*‖balance R U measured prepared x (peers i)‖≤cost i):
    scale*‖balance R U measured prepared x z‖≤∑i,‖μ i‖*cost i:=by
  rw [votes,map_sum]
  simp only [map_smul,smul_eq_mul]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hs).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _=>?_
  by_cases empty:μ i=0
  · simp only [empty,zero_mul,norm_zero,mul_zero,le_refl]
  · rw [norm_mul,mul_left_comm]
    exact mul_le_mul_of_nonneg_left (seated i empty) (norm_nonneg _)

end YM.Integration.WilsonPhysicalStationMixedWickRespondents
end
