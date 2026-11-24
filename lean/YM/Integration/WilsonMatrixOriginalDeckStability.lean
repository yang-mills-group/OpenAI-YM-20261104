import YM.Integration.WilsonMatrixOriginalDeckError

/-! Quantitative accumulation of signed full-field errors. The number of radii is arbitrary. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckStability
open Finset WilsonMatrixOriginalDeckPath WilsonMatrixOriginalDeckRelative WilsonMatrixOriginalDeckError
open scoped Classical BigOperators

private def reserve (A:ℝ) (d:ℕ→ℝ) (n:ℕ) : ℝ := ∏i∈range n, (1+A*d i)

private theorem accumulated (A:ℝ) (d:ℕ→ℝ) (n:ℕ) :
    1+(∑i∈range n,A*d i*reserve A d i)=reserve A d n := by
  induction n with
  | zero => simp [reserve]
  | succ n ih =>
    rw [sum_range_succ,←add_assoc,ih]
    change reserve A d n+A*d n*reserve A d n=∏i∈range (n+1),(1+A*d i)
    rw [prod_range_succ]
    change reserve A d n+_=reserve A d n*(1+A*d n)
    ring

private theorem exponential (A:ℝ) (d:ℕ→ℝ) (hA:0≤A) (hd:∀i,0≤d i) (n:ℕ) :
    reserve A d n≤Real.exp (A*(∑i∈range n,d i)) := by
  induction n with
  | zero => simp [reserve]
  | succ n ih =>
    rw [sum_range_succ,mul_add,Real.exp_add]
    change (∏i∈range (n+1), (1+A*d i))≤_
    rw [prod_range_succ]
    exact mul_le_mul ih (by simpa [add_comm] using Real.add_one_le_exp (A*d n))
      (add_nonneg (by norm_num) (mul_nonneg hA (hd n))) (Real.exp_pos _).le

variable {I:Type*} [Fintype I] [DecidableEq I]

/-- With exact forward subproduct cost A·w(j)/w(i), the whole signed error is at most
A²·w(N)·D·exp(A·D), where D is the sum of the full one-step error costs. -/
theorem measured (U:ℕ→ℕ→Matrix I I ℂ) (V:ℕ→Matrix I I ℂ) (w:ℕ→ℝ) (A:ℝ) (N:ℕ)
    (unit:∀i,U i i=1) (compose:∀i j k,U i j*U j k=U i k)
    (hA:0≤A) (w0:w 0=1) (nw:∀i,0≤w i) (increase:Monotone w)
    (paid:∀ n≤N,∀i≤n,amount (U n i)*w i≤A*w n) :
    let D := ∑i∈range N,amount (V i-U (i+1) i)
    amount (steps V N-U N 0) ≤ A^2*w N*D*Real.exp (A*D) := by
  classical
  let d := fun i=>amount (V i-U (i+1) i)
  have hd (i:ℕ) : 0≤d i := nonneg _
  have hres (i:ℕ) : 0≤reserve A d i := prod_nonneg fun t _ => add_nonneg (by norm_num) (mul_nonneg hA (hd t))
  have diff (n:ℕ) : amount (steps V n-U n 0) ≤ ∑i∈range n,amount (U n (i+1))*d i*amount (steps V i) := by
    rw [telescope U V unit compose n]
    apply (sum_cost _ _).trans
    exact sum_le_sum fun i _=>(product_cost _ _).trans (mul_le_mul_of_nonneg_right (product_cost _ _) (nonneg _))
  have term (n:ℕ) (hn:n≤N) (i:ℕ) (hi:i<n) (lower:amount (steps V i)≤A*w i*reserve A d i) :
      amount (U n (i+1))*d i*amount (steps V i) ≤ (A*w n)*(A*d i*reserve A d i) := by
    have tail : amount (U n (i+1))*w i≤A*w n :=
      (mul_le_mul_of_nonneg_left (increase (Nat.le_succ i)) (nonneg _)).trans (paid n hn (i+1) hi)
    calc amount (U n (i+1))*d i*amount (steps V i) ≤ amount (U n (i+1))*d i*(A*w i*reserve A d i) :=
           mul_le_mul_of_nonneg_left lower (mul_nonneg (nonneg _) (hd i))
         _ = (amount (U n (i+1))*w i)*(A*d i*reserve A d i) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right tail (mul_nonneg (mul_nonneg hA (hd i)) (hres i))
  have growth (n:ℕ) : n≤N → amount (steps V n) ≤ A*w n*reserve A d n := by
    induction n using Nat.strong_induction_on with
    | h n prior =>
      intro hn
      have err := (diff n).trans (sum_le_sum fun i hi => term n hn i (mem_range.mp hi)
        (prior i (mem_range.mp hi) (le_trans (mem_range.mp hi).le hn)))
      rw [←mul_sum] at err
      have base : amount (U n 0)≤A*w n := by simpa only [w0,mul_one] using paid n hn 0 (Nat.zero_le n)
      calc amount (steps V n) = amount ((steps V n-U n 0)+U n 0) := by rw [sub_add_cancel]
           _ ≤ amount (steps V n-U n 0)+amount (U n 0) := add_cost ..
           _ ≤ (A*w n)*(∑i∈range n,A*d i*reserve A d i)+A*w n := add_le_add err base
           _ = A*w n*(1+(∑i∈range n,A*d i*reserve A d i)) := by ring
           _ = _ := congrArg (fun b=>A*w n*b) (accumulated A d n)
  let D := ∑i∈range N,d i
  have cap (i:ℕ) (hi:i<N) : reserve A d i≤Real.exp (A*D) := by
    apply (exponential A d hA hd i).trans
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hA
    exact sum_le_sum_of_subset_of_nonneg (range_mono hi.le) (fun j _ _=>hd j)
  have total := (diff N).trans (sum_le_sum fun i hi => term N le_rfl i (mem_range.mp hi)
    (growth i (mem_range.mp hi).le))
  calc amount (steps V N-U N 0) ≤ ∑i∈range N,(A*w N)*(A*d i*reserve A d i) := total
       _ ≤ ∑i∈range N,(A*w N)*(A*d i*Real.exp (A*D)) := sum_le_sum fun i hi =>
         mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (cap i (mem_range.mp hi)) (mul_nonneg hA (hd i))) (mul_nonneg hA (nw N))
       _ = ∑i∈range N,(A^2*w N*Real.exp (A*D))*d i := sum_congr rfl fun _ _=>by ring
       _ = (A^2*w N*Real.exp (A*D))*D := (mul_sum ..).symm
       _ = _ := by dsimp only [D,d];ring

end YM.Integration.WilsonMatrixOriginalDeckStability
