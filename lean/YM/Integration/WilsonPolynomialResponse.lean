import YM.Marker.Truncated

/-! Finite-degree stability of the original marked multiplier. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonPolynomialResponse
open Marker
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
variable {w : V → ℝ} (hw : ∀ v, 0 < w v)

def slope (m : ℕ) (a : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m+1), (2*(a+1))^k / k.factorial

omit [Fintype V] in
include hw in
theorem power {a b : Poly R} {A : ℝ} (ha : Poly.price w a ≤ A) (hb : Poly.price w b ≤ A) (k : ℕ) :
    Poly.price w (a^k-b^k) ≤ (2*(A+1))^k * Poly.price w (a-b) := by
  have hA := (Poly.nonnegative hw a).trans ha
  have hD := Poly.nonnegative hw (a-b)
  have hB : A ≤ 2*(A+1) := by linarith
  induction k with
  | zero => simpa using hD
  | succ k ih =>
    have hpow := (Poly.powers hw b k).trans
      (pow_le_pow_left₀ (Poly.nonnegative hw b) (hb.trans hB) k)
    have hx := (Poly.multiplication hw (a^k-b^k) a).trans
      (mul_le_mul ih ha (Poly.nonnegative hw _) (mul_nonneg (pow_nonneg (hA.trans hB) k) hD))
    have hy := (Poly.multiplication hw (b^k) (a-b)).trans
      (mul_le_mul_of_nonneg_right hpow hD)
    calc
      _ = Poly.price w ((a^k-b^k)*a + b^k*(a-b)) := by congr 1; rw [pow_succ,pow_succ]; ring
      _ ≤ _ := (Poly.addition hw _ _).trans (add_le_add hx hy)
      _ ≤ _ := by
        rw [pow_succ]
        nlinarith [mul_nonneg (mul_nonneg (pow_nonneg (hA.trans hB) k) hD) (show 0 ≤ A+1 by linarith)]

include hw in
theorem multiplier {a b : Poly R} {A : ℝ} (ha : Poly.price w a ≤ A) (hb : Poly.price w b ≤ A) :
    Poly.price w (Poly.pass a-Poly.pass b) ≤ slope (Fintype.card V) A * Poly.price w (a-b) := by
  unfold Poly.pass slope
  rw [←Finset.sum_sub_distrib, Finset.sum_mul]
  apply (Poly.batch hw _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [←smul_sub, Poly.adapted]
  have h := mul_le_mul_of_nonneg_left (power hw ha hb k) (norm_nonneg ((k.factorial : ℂ)⁻¹))
  simpa [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h

theorem slope_bound (m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    slope m a ≤ (m+1 : ℕ) * (2*(a+1))^m := by
  have h1 : 1 ≤ 2*(a+1) := by linarith
  calc
    _ ≤ ∑ _k ∈ Finset.range (m+1), (2*(a+1))^m := by
      apply Finset.sum_le_sum
      intro k hk
      have hf : 1 ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
      exact (div_le_self (pow_nonneg (zero_le_one.trans h1) k) hf).trans
        (pow_le_pow_right₀ h1 (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    _ = _ := by simp

end YM.Integration.WilsonPolynomialResponse
end
