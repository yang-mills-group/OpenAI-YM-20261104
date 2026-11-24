import YM.Integration.WilsonPositionProgramRadialPrices

/-! Reprice a signed submitted row through the actual clock on both submitted angular charts. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramDatedClockBill
open Finset Comparison.RG02 Comparison.RG02.Adjacent Comparison.RG02.Moving.Path
open WilsonPositionProgramRadialPrices
open scoped Classical BigOperators
variable {E B:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def cost (T:UnitCost)(d:ℤ)(r k:ℕ)(height:ℕ→ℕ)(w:ℕ→ℕ→ℝ):ℝ:=
  ∑ i∈range (r+1),∑ j∈range (height i+1),
    ‖motion (money T d i j) k‖ *
      ∑ a∈range (height i+1),‖factor (height i) j a‖ * w i a

theorem signed (T:UnitCost)(d:ℤ)(r k:ℕ)(height:ℕ→ℕ)(U:Display E)(V:Display B)
    (hu:Charge r (fun j=>(height j:ℤ)) U)(hv:Charge r (fun j=>(height j:ℤ)) V)
    (x y:E)(b c:B):
    born U T d r k x-born U T d r k y-(born V T d r k b-born V T d r k c)=
      ∑ i∈range (r+1),∑ j∈range (height i+1),motion (money T d i j) k *
        ∑ a∈range (height i+1),factor (height i) j a *
          (U i ((a:ℝ) • x)-U i ((a:ℝ) • y)-(V i ((a:ℝ) • b)-V i ((a:ℝ) • c))):=by
  simp only [message T d r hu, message T d r hv, Int.toNat_natCast, ←sum_sub_distrib, ←mul_sub]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [centered (height i) j (mem_range_succ_iff.mp hj) (U i) (hu i (mem_range_succ_iff.mp hi)),
    centered (height i) j (mem_range_succ_iff.mp hj) (V i) (hv i (mem_range_succ_iff.mp hi)),
    ←sum_sub_distrib]
  simp only [←mul_sub]

theorem original (T:UnitCost)(d:ℤ)(r k:ℕ)(height:ℕ→ℕ)(U:Display E)(V:Display B)
    (hu:Charge r (fun j=>(height j:ℤ)) U)(hv:Charge r (fun j=>(height j:ℤ)) V)
    (x y:E)(b c:B)(w:ℕ→ℕ→ℝ)
    (reading:∀i≤r,∀a≤height i,
      ‖U i ((a:ℝ) • x)-U i ((a:ℝ) • y)-(V i ((a:ℝ) • b)-V i ((a:ℝ) • c))‖≤w i a):
    ‖born U T d r k x-born U T d r k y-(born V T d r k b-born V T d r k c)‖≤
      cost T d r k height w:=by
  rw [signed T d r k height U V hu hv]
  refine (norm_sum_le ..).trans (sum_le_sum fun i hi=>?_)
  refine (norm_sum_le ..).trans (sum_le_sum fun j _=>?_)
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_sum_le ..).trans (sum_le_sum fun a ha=>?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (reading i (mem_range_succ_iff.mp hi) a
    (mem_range_succ_iff.mp ha)) (norm_nonneg _)

end YM.Integration.WilsonPositionProgramDatedClockBill
end
