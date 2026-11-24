import YM.Integration.WilsonReceivedSingletonWindow

/-! Payment of the disconnected part of the signed ordinary pair at the
original source weights. The fitted counterterm has its own singleton fee. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedOrdinaryPayment

theorem unweight {g w M : ℝ} (hg : 0 < g) (hw : 0 < w) (fee : g * (w * M) ≤ 1) :
    M ≤ (g*w)⁻¹ := by
  rw [← one_div]
  apply (le_div_iff₀ (mul_pos hg hw)).2
  simpa only [mul_comm,mul_assoc,mul_left_comm] using fee

/-- The signed four-face estimate after using the actual source tolls on the
two means and both coefficient masses. All four regular errors stay separate. -/
theorem numeric {g wa wb err es ec ea eb ta tb ma mb : ℝ} {r : ℕ}
    (hg : 0 < g) (ha : 0 < wa) (hb : 0 < wb) (eA : 0 ≤ ea) (eB : 0 ≤ eb)
    (mB : 0 ≤ mb)
    (meansA : g*(wa*ta) ≤ 1) (meansB : g*(wb*tb) ≤ 1)
    (massA : g*(wa*ma) ≤ 1) (massB : g*(wb*mb) ≤ 1)
    (reading : err ≤ es+ec+ea*(tb+eb)+ta*eb+g^(r+1)*(ma*mb)) :
    err ≤ es+ec+ea*((g*wb)⁻¹+eb)+(g*wa)⁻¹*eb+
      g^(r+1)*((g*wa)⁻¹*(g*wb)⁻¹) := by
  apply reading.trans
  apply add_le_add
  · apply add_le_add
    · apply add_le_add_right
      exact mul_le_mul_of_nonneg_left (add_le_add_left (unweight hg hb meansB) eb) eA
    · exact mul_le_mul_of_nonneg_right (unweight hg ha meansA) eB
  · exact mul_le_mul_of_nonneg_left (mul_le_mul (unweight hg ha massA) (unweight hg hb massB)
      mB (inv_nonneg.mpr (mul_pos hg ha).le)) (pow_nonneg hg.le _)

end YM.Integration.WilsonReceivedOrdinaryPayment
