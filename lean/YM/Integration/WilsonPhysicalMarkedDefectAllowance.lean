import YM.Ac.Tree

/-! Price the empty ordinary source at a strictly positive amount as required
by the original one-step theorem. The whole geometric expense is paid out of
a *single* power of the original fine coupling. -/

namespace YM.Integration.WilsonPhysicalMarkedDefect

noncomputable def emptyAllowance (expense : ℝ) (count : ℕ) (power : ℝ) : ℝ :=
  min 1 (power / (8*(1+|expense|)^count))

theorem empty_allowance (expense : ℝ) (count : ℕ) {power : ℝ} (hp : 0 < power) :
    0 < emptyAllowance expense count power ∧ emptyAllowance expense count power ≤ 1 ∧
    8*expense^count * emptyAllowance expense count power + 17*power ≤ 18*power := by
  have hd : 0 < (8:ℝ)*(1+|expense|)^count := by positivity
  have ha : 0 < emptyAllowance expense count power := lt_min zero_lt_one (div_pos hp hd)
  have h1 : expense^count ≤ (1+|expense|)^count := by
    calc
      _ ≤ |expense^count| := le_abs_self _
      _ = |expense|^count := abs_pow _ _
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (by linarith) _
  have h2 : (8*expense^count) * emptyAllowance expense count power ≤ power := by
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by norm_num)) ha.le).trans
      ((le_div_iff₀ hd).mp (min_le_right _ _))
  exact ⟨ha,min_le_left _ _,by linarith⟩

end YM.Integration.WilsonPhysicalMarkedDefect

