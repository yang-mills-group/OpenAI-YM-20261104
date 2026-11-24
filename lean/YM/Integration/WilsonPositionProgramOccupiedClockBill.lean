import YM.Integration.WilsonPositionProgramDatedClockBill

/-! Reprice a full occupied face, including the scalar at its actual marked roots. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramOccupiedClockBill
open Finset Polynomial Comparison.RG02 Comparison.RG02.Valence Comparison.RG02.Assembly
open Comparison.RG02.Adjacent Comparison.RG02.Moving.Path WilsonPositionProgramRadialPrices
open scoped Classical BigOperators
variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem radial (D k : ℕ) (hk : k ≤ D) (F : E → ℂ) (fund : Level D F) (x : E) :
    Assembly.jet F k x=∑ a∈range (D+1), factor D k a * F ((a:ℝ) • x) := by
  let P : Polynomial ℂ := ∑ j∈range (D+1), monomial j (Assembly.jet F j x)
  have degree : P.natDegree ≤ D := by
    apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_monomial_le _).trans (mem_range_succ_iff.mp hj)
  have short : P.degree < (D+1:ℕ) := degree_le_natDegree.trans_lt
    (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le degree))
  have coeff := congrArg (fun q : Polynomial ℂ => q.coeff k)
    (Lagrange.eq_interpolate (s:=range (D+1)) (v:=((↑):ℕ→ℂ)) Nat.cast_injective.injOn
      (f:=P) (by simpa using short))
  have left : P.coeff k = Assembly.jet F k x := by simp [P,coeff_monomial,hk]
  rw [left] at coeff
  change Assembly.jet F k x=(∑ a∈range (D+1), C (P.eval (a:ℂ)) *
    Lagrange.basis (range (D+1)) ((↑):ℕ→ℂ) a).coeff k at coeff
  rw [coeff, finsetSum_coeff]
  apply sum_congr rfl
  intro a _
  rw [coeff_C_mul, mul_comm]
  change WilsonPositionProgramRadialPrices.factor D k a * P.eval (a:ℂ) = _
  congr 1
  rw [fund.posted ((a:ℝ) • x)]
  simp only [P,Polynomial.eval_finsetSum,eval_monomial]
  apply sum_congr rfl
  intro j _
  simp [Clipper.weight,Complex.real_smul,mul_comm]

theorem signed (T : UnitCost) (d : ℤ) (r k : ℕ) (height : ℕ → ℕ)
    (U : Display E) (V : Display B)
    (hu : Charge r (fun j=>(height j:ℤ)) U) (hv : Charge r (fun j=>(height j:ℤ)) V)
    (x : E) (b : B) :
    born U T d r k x-born V T d r k b =
      ∑ i∈range (r+1),∑ j∈range (height i+1),motion (money T d i j) k *
        ∑ a∈range (height i+1),factor (height i) j a *
          (U i ((a:ℝ) • x)-V i ((a:ℝ) • b)) := by
  simp only [message T d r hu, message T d r hv, Int.toNat_natCast, ←sum_sub_distrib, ←mul_sub]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [radial (height i) j (mem_range_succ_iff.mp hj) (U i) (hu i (mem_range_succ_iff.mp hi)),
    radial (height i) j (mem_range_succ_iff.mp hj) (V i) (hv i (mem_range_succ_iff.mp hi)),
    ←sum_sub_distrib]
  simp only [←mul_sub]

theorem original (T : UnitCost) (d : ℤ) (r k : ℕ) (height : ℕ → ℕ)
    (U : Display E) (V : Display B)
    (hu : Charge r (fun j=>(height j:ℤ)) U) (hv : Charge r (fun j=>(height j:ℤ)) V)
    (x : E) (b : B) (w : ℕ→ℕ→ℝ)
    (reading : ∀i≤r,∀a≤height i, ‖U i ((a:ℝ) • x)-V i ((a:ℝ) • b)‖ ≤ w i a) :
    ‖born U T d r k x-born V T d r k b‖ ≤ WilsonPositionProgramDatedClockBill.cost T d r k height w := by
  rw [signed T d r k height U V hu hv]
  refine (norm_sum_le ..).trans (sum_le_sum fun i hi=>?_)
  refine (norm_sum_le ..).trans (sum_le_sum fun j _=>?_)
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_sum_le ..).trans (sum_le_sum fun a ha=>?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (reading i (mem_range_succ_iff.mp hi) a
    (mem_range_succ_iff.mp ha)) (norm_nonneg _)

end YM.Integration.WilsonPositionProgramOccupiedClockBill
end
