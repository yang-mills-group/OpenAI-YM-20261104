import YM.Integration.WilsonIndependentRestoredElectionStock

set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonIndependentRestoredPublicRates

open Filter Lattice
open scoped Topology

/-- One positive election at all grades. The stage exponent eventually absorbs
each fixed block-length restoration at the actual selected side. -/
def tolerance (L : Side) (j _d : ℕ) : ℝ :=
  (1 / ((j : ℝ) + 1)) / (L.val : ℝ)^j

theorem positive (L : Side) (j d : ℕ) : 0 < tolerance L j d := by
  have hL : 0 < (L.val : ℝ) := by exact_mod_cast L.pos
  unfold tolerance
  positivity

theorem priced (L : Side) {h j : ℕ} (hj : h ≤ j) (d : ℕ) :
    (L.val : ℝ)^h * tolerance L j d ≤ 1 / ((j : ℝ) + 1) := by
  have hL : (1 : ℝ) ≤ (L.val : ℝ) := by exact_mod_cast L.pos
  have hp := pow_le_pow_right₀ hL hj
  have h₀ : 0 < (L.val : ℝ)^j := pow_pos (lt_of_lt_of_le zero_lt_one hL) _
  calc
    _ = (1 / ((j : ℝ) + 1)) * ((L.val : ℝ)^h / (L.val : ℝ)^j) := by
      unfold tolerance
      ring
    _ ≤ (1 / ((j : ℝ) + 1)) * 1 :=
      mul_le_mul_of_nonneg_left ((div_le_one h₀).mpr hp) (by positivity)
    _ = _ := mul_one _

theorem uniform (h : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∀ (L : Side) (d : ℕ), (L.val : ℝ)^h * tolerance L j d < ε := by
  obtain ⟨n,hn⟩ := exists_nat_gt (1 / ε)
  filter_upwards [eventually_ge_atTop (max h n)] with j hj L d
  have hr : (1 / ε) < (j : ℝ) + 1 :=
    lt_of_lt_of_le hn (by exact_mod_cast (show n ≤ j+1 from
      ((le_max_right h n).trans hj).trans (Nat.le_succ j)))
  have hp : 1 < ε * ((j : ℝ) + 1) := by
    rw [mul_comm]
    exact (div_lt_iff₀ hε).mp hr
  exact (priced L ((le_max_left h n).trans hj) d).trans_lt
    ((div_lt_iff₀ (show (0:ℝ)<(j:ℝ)+1 by positivity)).mpr hp)

end YM.Integration.WilsonIndependentRestoredPublicRates

