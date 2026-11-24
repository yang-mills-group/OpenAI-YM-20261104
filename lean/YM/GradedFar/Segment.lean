import YM.GradedFar.Register
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-! # Receipts on little paths of compact shape variables -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open FVA2.GradedFar FVA2.GradedFar.Cart Function Filter Set MeasureTheory PowerSeries
open scoped Topology BigOperators Classical Interval
variable {X:Type*}{L:Filter X}{t:X→ℝ}{f:X→ℝ→ℂ}{F:ℝ→PowerSeries ℂ}{a b:ℝ}

def operand (a b:ℝ)(f:ℝ→PowerSeries ℂ) := PowerSeries.mk (fun i=> ∫ x in a..b, coeff i (f x))
lemma integrates (h:Receives t L (fun r (x:↥(uIcc a b))=> f r x.val) (fun x=> F x.val))
    (hv:∀ᶠ r in L, IntervalIntegrable (f r) volume a b)
    (hp:∀ i,IntervalIntegrable (fun x=> coeff i (F x)) volume a b) : Expansion t L (fun r=> ∫ x in a..b,f r x) (operand a b F):=by
 refine ⟨fun i=> Charge.const _,fun p=>?_⟩; obtain ⟨C,hC,H⟩:= (h.good p).cost; let T:= Finset.range (p+1)
 refine ⟨C*|b-a|, mul_nonneg hC (abs_nonneg _),?_⟩; filter_upwards [H,hv] with r hr hv i
 have he j : IntervalIntegrable (fun x=> (t r :ℂ)^j*coeff j (F x)) volume a b:=(hp j).const_mul _
 have hu: crop p (t r) (operand a b F)= ∫ x in a..b,crop p (t r) (F x):=by
   simp_rw [crop_eq,operand,coeff_mk, ← intervalIntegral.integral_const_mul]
   rw [intervalIntegral.integral_finsetSum fun i _=> he i]
 have hP: IntervalIntegrable (fun x=> crop p (t r) (F x)) volume a b:=by simp_rw [crop_eq]; rw [show (fun x=> ∑ k∈Finset.range (p+1),(t r:ℂ)^k*coeff k (F x))= (∑ k∈Finset.range (p+1),fun x=>(t r:ℂ)^k*coeff k (F x)) from funext fun x=> by rw [Finset.sum_apply] ]; exact IntervalIntegrable.sum T (fun i _=> he i)
 rw [hu,← intervalIntegral.integral_sub hv hP]; exact (intervalIntegral.norm_integral_le_of_norm_le_const
    (fun i hi=> hr (⟨i,uIoc_subset_uIcc hi⟩: uIcc a b))).trans_eq (by ring)
end YM.Integration.GradedFar
