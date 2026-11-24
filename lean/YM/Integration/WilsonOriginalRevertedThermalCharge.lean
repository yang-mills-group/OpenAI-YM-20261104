import YM.Integration.WilsonPositionProgramDatedClockBill

/-! Absolute finite change of the thermal clock, including the value at zero direction. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalRevertedThermalCharge
open Finset Polynomial Comparison.RG02 Comparison.RG02.Assembly Comparison.RG02.Valence
open Comparison.RG02.Adjacent WilsonPositionProgramRadialPrices WilsonPositionProgramDatedClockBill
open Finset Comparison.RG02 Comparison.RG02.Adjacent Comparison.RG02.Moving.Path
open scoped Classical BigOperators
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem coefficient (D k:ℕ)(u:ℕ→ℂ)(hk:k≤D):
    u k=∑ a∈range (D+1), factor D k a * (∑ j∈range (D+1), (a:ℂ)^j * u j):=by
  let P:Polynomial ℂ:=∑ j∈range (D+1),Polynomial.monomial j (u j)
  have degree:P.natDegree≤D:=by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (Polynomial.natDegree_monomial_le (u j)).trans (mem_range_succ_iff.mp hj)
  have small:P.degree<(D+1:ℕ):=Polynomial.degree_le_natDegree.trans_lt
    (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le degree))
  have same:=congrArg (fun q:Polynomial ℂ=>q.coeff k)
    (Lagrange.eq_interpolate (s:=range (D+1)) (v:=((↑):ℕ→ℂ)) Nat.cast_injective.injOn
      (f:=P) (by simpa using small))
  have left:P.coeff k=u k:=by
    simp [P,Polynomial.coeff_monomial,hk]
  rw [left] at same
  change u k=(∑ a∈range (D+1),Polynomial.C (P.eval (a:ℂ)) *
    Lagrange.basis (range (D+1)) ((↑):ℕ→ℂ) a).coeff k at same
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul] at same
  simpa [WilsonPositionProgramRadialPrices.factor,P,Polynomial.eval_finsetSum,mul_comm] using same

theorem radial (D j:ℕ)(hj:j≤D)(U V:E→ℂ)(left:Level D U)(right:Level D V)(x:E):
    Assembly.jet U j x-Assembly.jet V j x=
      ∑ a∈range (D+1),factor D j a * (U ((a:ℝ) • x)-V ((a:ℝ) • x)):=by
  rw [coefficient D j (fun z=>Assembly.jet U z x-Assembly.jet V z x) hj]
  apply sum_congr rfl
  intro a _
  rw [left.posted ((a:ℝ) • x),right.posted ((a:ℝ) • x),←sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro n _
  simp [Clipper.weight,Complex.real_smul,mul_sub]

theorem restored (T:UnitCost)(d:ℤ)(r k:ℕ)(height:ℕ→ℕ)(U V:Display E)
    (hu:Charge r (fun i=>(height i:ℤ)) U)(hv:Charge r (fun i=>(height i:ℤ)) V)(x:E):
    born U T d r k x-born V T d r k x=
      ∑ i∈range (r+1),∑ j∈range (height i+1),motion (money T d i j) k *
        ∑ a∈range (height i+1),factor (height i) j a*(U i ((a:ℝ) • x)-V i ((a:ℝ) • x)):=by
  simp only [message T d r hu,message T d r hv,Int.toNat_natCast,←sum_sub_distrib,←mul_sub]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [radial (height i) j (mem_range_succ_iff.mp hj) (U i) (V i)
    (hu i (mem_range_succ_iff.mp hi)) (hv i (mem_range_succ_iff.mp hi)) x]

theorem original (T:UnitCost)(d:ℤ)(r k:ℕ)(height:ℕ→ℕ)(U V:Display E)
    (hu:Charge r (fun i=>(height i:ℤ)) U)(hv:Charge r (fun i=>(height i:ℤ)) V)(x:E)
    (w:ℕ→ℕ→ℝ)(reading:∀i≤r,∀a≤height i,‖U i ((a:ℝ) • x)-V i ((a:ℝ) • x)‖≤w i a):
    ‖born U T d r k x-born V T d r k x‖≤cost T d r k height w:=by
  rw [restored T d r k height U V hu hv]
  refine (norm_sum_le ..).trans (sum_le_sum fun i hi=>?_)
  refine (norm_sum_le ..).trans (sum_le_sum fun j _=>?_)
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_sum_le ..).trans (sum_le_sum fun a ha=>?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (reading i (mem_range_succ_iff.mp hi) a
    (mem_range_succ_iff.mp ha)) (norm_nonneg _)


end YM.Integration.WilsonOriginalRevertedThermalCharge
end
