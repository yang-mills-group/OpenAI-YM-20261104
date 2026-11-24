import YM.MatchingLedger.Books.Jets
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Finite coefficient operations

Exponential of the strictly positive-degree exponent. We write even this
out in finite arithmetic. Compatibility in perturbative order is then transparent.
Not identifying any analytic function by an infinite series expansion!
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Books.FPS
open Function Filter Matrix Finset PowerSeries
open scoped Topology Classical BigOperators

lemma triple {A : Type*} [AddCommMonoid A] (f : ℕ → ℕ → ℕ → A) (n : ℕ) :
      (∑ i∈ antidiagonal n, ∑ j∈ antidiagonal i.1, f j.1 j.2 i.2)=
           ∑ i∈ antidiagonal n, ∑ j∈antidiagonal i.2, f i.1 j.1 j.2 := by
  -- adapt MSBar Ward Route (not importing formal theory)
  rw [sum_sigma' (t:=fun i:ℕ×ℕ=>antidiagonal i.1) (f:=fun i j=> f j.1 j.2 i.2),
    sum_sigma' (t:=fun i:ℕ×ℕ=>antidiagonal i.2) (f:=fun i j=> f i.1 j.1 j.2)]
  refine sum_nbij' (fun i=> ⟨(i.2.1,i.2.2+i.1.2),(i.2.2,i.1.2)⟩) (fun i=> ⟨(i.1.1+i.2.1,i.2.2),(i.1.1,i.2.1)⟩) ?_ ?_ ?_ ?_ (fun i _=>rfl)
  all_goals rintro ⟨⟨a,b⟩,c,d⟩ h; simp at *
  all_goals omega

variable {ι : Type*} (V : ℕ → Poly ι)

/-- `V 0` is the (possibly source-tilted) quadratic, *not included* here. -/
def higher : ℕ → Poly ι | 0 => 0 | i+1=> V (i+1)
def roll : PowerSeries (Poly ι) := PowerSeries.mk (fun i=> - higher V i)
def driver (k n : ℕ) : Poly ι := (k.factorial:ℝ)⁻¹ • coeff n (roll V ^ k)
def thermal (n : ℕ) := ∑ k∈range (n+1), driver V k n

lemma driver_zero (k n : ℕ)(h:n < k): driver V k n=0:=by
  have he : X∣ roll V := by
    have he : X^1 ∣ roll V:= X_pow_dvd_iff.mpr fun m h=>by
      have hx : m=0 := by omega
      simp [hx,higher,roll]
    rwa [pow_one] at he
  have ht:X^k ∣ roll V ^ k:= pow_dvd_pow_of_dvd he _
  unfold driver; rw [(X_pow_dvd_iff.mp ht) _ h,smul_zero]
lemma thermal_extend (i : ℕ) {N:ℕ} (h:i ≤ N): thermal V i=∑ k∈range (N+1), driver V k i:= by
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right h _)); intro k _ hk
  exact driver_zero V k i (by rw [mem_range] at hk; omega)
lemma thermal_one : thermal V 0=1:=by simp [thermal,driver]

private def partD (j:ι)(A:PowerSeries (Poly ι)) : PowerSeries (Poly ι):= PowerSeries.mk (fun i=> (MvPolynomial.pderiv j) (coeff i A))
private lemma partD_mul (j:ι)(A B:PowerSeries (Poly ι)): partD j (A*B)= A * partD j B + partD j A * B:= by
  apply PowerSeries.ext; intro n; simp only [partD, coeff_mk, coeff_mul,_root_.map_sum,_root_.map_add,MvPolynomial.pderiv_mul,Finset.sum_add_distrib]; exact add_comm ..

private lemma partD_power (j:ι) (k:ℕ) : partD j (roll V^(k+1))=(k+1) • (partD j (roll V)* roll V^k):=by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    calc
      _ = _ := by rw [pow_succ (roll V) (k+1),partD_mul,ih] 
      _ = _ := by rw [add_smul,one_smul, pow_succ]; ring
private lemma driver_deriv (j:ι)(k n:ℕ) : MvPolynomial.pderiv j (driver V (k+1) n)=
    ∑ i ∈ antidiagonal n, -(MvPolynomial.pderiv j (higher V i.1) * driver V k i.2):= by
  unfold driver
  have hx := DFunLike.congr_arg (coeff n) (partD_power V j k)
  unfold partD at hx; rw [coeff_mk, map_nsmul] at hx; simp only [coeff_mul, coeff_mk] at hx
  rw [(MvPolynomial.pderiv j).map_smul,hx]; simp_rw [show ∀ n, coeff n (roll V)= -higher V n from fun n=> coeff_mk ..,_root_.map_neg,neg_mul]
  rw [Nat.factorial_succ]
  -- scalars
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]; rw [show (↑((k+1)*k.factorial):ℝ)⁻¹ * ↑(k+1:ℕ)=(k.factorial:ℝ)⁻¹ by push_cast; field_simp]; rw [Finset.smul_sum]; simp only [smul_neg,Algebra.mul_smul_comm]
lemma current (j:ι)(n:ℕ) : MvPolynomial.pderiv j (thermal V n) = -(∑ i∈antidiagonal n,MvPolynomial.pderiv j (higher V i.1)*thermal V i.2):= by
  rw [thermal_extend V n (Nat.le_succ n), _root_.map_sum,sum_range_succ']; simp_rw [driver_deriv]; have he:MvPolynomial.pderiv j (driver V 0 n)=0:=by
     rcases eq_or_ne n 0 with he|he <;> simp [driver,he,coeff_one]
  rw [he,add_zero,Finset.sum_comm]
  simp_rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl (fun i hi=>?_)
  have ht := mem_antidiagonal.mp hi; rw [thermal_extend V i.2 (N:=n) (by omega),mul_sum,Finset.sum_neg_distrib]
end YM.MatchingLedger.Books.FPS
