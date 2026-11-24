import YM.Integration.WilsonTrueProjectedPointInverse

/-! A fixed-order product of the dated inverse matrices can have many diagonal
steps. Only finitely many strict steps can occur along one coefficient path. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedTriangularFare
open Finset Matrix
open scoped Classical BigOperators
variable {E : Type*} [Fintype E]

theorem step (tier : E → ℕ) (A : Matrix E E ℂ) (v : E → ℂ)
    (diagonal : ∀ u, ‖A u u‖ ≤ 1)
    (strict : ∀ u b, u ≠ b → A u b ≠ 0 → tier b < tier u)
    (H B t : ℝ) (hp : 0 ≤ H) (fund : 0 ≤ B) (base : 1 ≤ t)
    (fee : ∀ u b, ‖A u b‖ ≤ H) (wage : ∀ b, ‖v b‖ ≤ B*t^(tier b)) (u : E) :
    ‖(A *ᵥ v) u‖ ≤ B*(t+(Fintype.card E:ℝ)*H)^(tier u) := by
  classical
  let cost : ℝ := (Fintype.card E:ℝ)*H
  have cost_nn : 0 ≤ cost := mul_nonneg (Nat.cast_nonneg _) hp
  have tpos : 0 ≤ t := le_trans zero_le_one base
  have grow : t ≤ t+cost := le_add_of_nonneg_right cost_nn
  have stay : ‖A u u*v u‖ ≤ B*t^(tier u) := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (diagonal u) (norm_nonneg _)).trans (by simpa using wage u)
  by_cases zero : tier u=0
  · have alone : (A *ᵥ v) u = A u u*v u := by
      change ∑ b, A u b*v b=_
      apply Finset.sum_eq_single u
      · intro b _ different
        have hz : A u b=0 := by
          by_contra nonzero
          have h := strict u b different.symm nonzero
          omega
        rw [hz,zero_mul]
      · simp
    rw [alone]
    simpa [zero] using stay
  let r := tier u-1
  have rank : tier u=r+1 := by dsimp only [r]; omega
  have old (b : E) (different : b ≠ u) :
      ‖A u b*v b‖ ≤ H*(B*t^r) := by
    by_cases hz : A u b=0
    · simp only [hz,zero_mul,norm_zero]
      exact mul_nonneg hp (mul_nonneg fund (pow_nonneg tpos _))
    have smaller := strict u b different.symm hz
    have level : tier b ≤ r := by omega
    rw [norm_mul]
    exact mul_le_mul (fee u b)
      ((wage b).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ base level) fund))
      (norm_nonneg _) hp
  have others : (∑ b ∈ univ.erase u, ‖A u b*v b‖) ≤ cost*(B*t^r) := by
    calc
      _ ≤ ∑ _b ∈ univ.erase u, H*(B*t^r) := sum_le_sum (fun b hb => old b (mem_erase.mp hb).1)
      _ ≤ ∑ _b : E, H*(B*t^r) := sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset _ _) (fun _ _ _ => mul_nonneg hp (mul_nonneg fund (pow_nonneg tpos _)))
      _ = _ := by simp [cost,mul_assoc]
  calc
    ‖(A *ᵥ v) u‖ ≤ ∑ b, ‖A u b*v b‖ := norm_sum_le univ _
    _ = (∑ b ∈ univ.erase u, ‖A u b*v b‖)+‖A u u*v u‖ := (sum_erase_add _ _ (mem_univ u)).symm
    _ ≤ cost*(B*t^r)+ B*t^(tier u) := add_le_add others stay
    _ = B*(t+cost)*t^r := by rw [rank,pow_succ];ring
    _ ≤ B*(t+cost)*(t+cost)^r := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ tpos grow r) (mul_nonneg fund (tpos.trans grow))
    _ = _ := by rw [rank,pow_succ];dsimp only [cost];ring

theorem window (tier : E → ℕ) (A : ℕ → Matrix E E ℂ) (v : ℕ → E → ℂ)
    (first count : ℕ) (H B : ℝ) (hp : 0 ≤ H) (fund : 0 ≤ B)
    (start : ∀ b, ‖v first b‖ ≤ B)
    (next : ∀ j, first ≤ j → j < first+count → v (j+1)=A j *ᵥ v j)
    (diagonal : ∀ j, first ≤ j → j < first+count → ∀ u, ‖A j u u‖ ≤ 1)
    (strict : ∀ j, first ≤ j → j < first+count → ∀ u b, u ≠ b → A j u b ≠ 0 → tier b < tier u)
    (fee : ∀ j, first ≤ j → j < first+count → ∀ u b, ‖A j u b‖ ≤ H) (u : E) :
    ‖v (first+count) u‖ ≤ B*(1+(Fintype.card E:ℝ)*H*count)^(tier u) := by
  have all (n : ℕ) (live : n≤count) (b : E) :
      ‖v (first+n) b‖ ≤ B*(1+(Fintype.card E:ℝ)*H*n)^(tier b) := by
    induction n generalizing b with
    | zero => simpa using start b
    | succ n ih =>
      have begin' : first ≤ first+n := Nat.le_add_right _ _
      have end' : first+n < first+count := by omega
      have nonneg : 0 ≤ (Fintype.card E:ℝ)*H*(n:ℝ) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hp) (Nat.cast_nonneg _)
      rw [Nat.add_succ, next (first+n) begin' end']
      have bound := step tier (A (first+n)) (v (first+n))
        (diagonal _ begin' end') (strict _ begin' end') H B _ hp fund
        (le_add_of_nonneg_right nonneg) (fee _ begin' end') (ih (by omega)) b
      convert bound using 1
      push_cast
      ring
  exact all count le_rfl u

end YM.Integration.WilsonTrueProjectedTriangularFare
