import Mathlib.Tactic

/-!
Choose the truncation order separately for each signed coupling power.
The required contact order is reached without increasing the power cap
beyond max(oldCap, r+2). Positive shifts preserve the original lower
power bound, so one clearing power can be retained across all orders.
-/
set_option autoImplicit false

namespace YM.Integration.ActualBetaCutoff

def retuningOrder (r : ℕ) (e : ℤ) : ℕ :=
  (r + 1 - e.toNat + 1) / 2

theorem sufficient (r : ℕ) (e : ℤ) :
    r < e.toNat + 2 * retuningOrder r e := by
  unfold retuningOrder
  omega

theorem grid_bound (r : ℕ) (e : ℤ) :
    retuningOrder r e ≤ (r + 2) / 2 := by
  unfold retuningOrder
  omega

theorem zero_iff (r : ℕ) (e : ℤ) :
    retuningOrder r e = 0 ↔ r < e.toNat := by
  unfold retuningOrder
  omega

theorem shifted_power_bound (r cap : ℕ) (e : ℤ)
    (he : |e| ≤ (cap : ℤ)) (j : ℕ) (hj : j ≤ retuningOrder r e) :
    |e + 2 * (j : ℤ)| ≤ ((max cap (r + 2) : ℕ) : ℤ) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp he
  unfold retuningOrder at hj
  apply abs_le.mpr
  constructor <;> omega

theorem lower_preserved (bound : ℕ) (e : ℤ)
    (he : -(bound : ℤ) ≤ e) (j : ℕ) :
    -(bound : ℤ) ≤ e + 2 * (j : ℤ) := by
  omega

theorem clearing_preserved (B : ℕ) (e : ℤ)
    (he : 0 < (B : ℤ) + e) (j : ℕ) :
    0 < (B : ℤ) + (e + 2 * (j : ℤ)) := by
  omega

theorem cleared_grade (B : ℕ) (e : ℤ)
    (he : 0 ≤ (B : ℤ) + e) :
    ((B : ℤ) + e).toNat + (-e).toNat = B + e.toNat := by
  omega

end YM.Integration.ActualBetaCutoff
