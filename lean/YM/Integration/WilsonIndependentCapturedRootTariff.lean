import YM.Integration.WilsonIndependentCapturedRocketPrice

/-! The actual quadratic root tariff at the capture page is dominated by
a single exponential length charge on the common occupied word. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentCapturedRootTariff
open RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Spatial
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open scoped ENNReal
def cost (D ρ : ℝ) := (1+2*D+8/ρ)^2

theorem square {s D ρ : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ D) (hr : 0 < ρ) :
    (1+2*(s+D))^2 ≤ cost D ρ * Real.exp (ρ*s/2) := by
  let k := 1+2*D+8/ρ
  have wide : 8/ρ ≤ k := by dsimp [k]; linarith
  have kp : 0 ≤ k := (div_nonneg (by norm_num) hr.le).trans wide
  have lower : 1+2*D ≤ k := by dsimp [k]; linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 8) hr.le]
  have side : (8/ρ)*(ρ*s/4)=2*s := by field_simp; ring
  have edge : 1+2*(s+D) ≤ k*Real.exp (ρ*s/4) := by
    calc
      _ = (1+2*D)+2*s := by ring
      _ ≤ k+k*(ρ*s/4) := add_le_add lower (side ▸ mul_le_mul_of_nonneg_right wide (by positivity))
      _ = k*(ρ*s/4+1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) kp
  have doubled := pow_le_pow_left₀ (show 0 ≤ 1+2*(s+D) by positivity) edge 2
  rw [mul_pow, sq (Real.exp _),←Real.exp_add,show ρ*s/4+ρ*s/4=ρ*s/2 by ring] at doubled
  exact doubled

variable {W : Type} {M : W → ℕ} {X Y : Page M → Type} (S : Sky X Y)
theorem atPage (root : W → Room) (page : Page M) {r : ℕ} (x : Tuple (X page) r)
    {s D ρ : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ D) (hr : 0 < ρ)
    (reaches : ∀ j, dist (root page.bindW) ((S.maps page).pos (x j)) ≤ (s+D)*S.radius page) :
    (S.coverQ root 2 page).width x ≤ ENNReal.ofReal (cost D ρ * Real.exp (ρ*s/2)) := by
  let bound := ENNReal.ofReal (cost D ρ * Real.exp (ρ*s/2))
  have dim {d : ℝ} (near : d ≤ 2*(s+D)*S.radius page) :
      Tariff.amount (S.radius page) 2 d ≤ bound := by
    refine (Tariff.amount_mono (S.radius_pos page) 2 near).trans ?_
    change ENNReal.ofReal (1+(2*(s+D)*S.radius page)/S.radius page)^2 ≤ _
    rw [mul_div_cancel_right₀ _ (S.radius_pos page).ne',← ENNReal.ofReal_pow (by positivity)]
    exact ENNReal.ofReal_le_ofReal (square hs hd hr)
  have width : 1 ≤ bound := by
    have h := dim (show (0:ℝ) ≤ 2*(s+D)*S.radius page by have h := (S.radius_pos page).le; positivity)
    simpa only [Tariff.amount_zero] using h
  refine (S.coverQ root 2 page).width_le ?_ ?_
  · apply Tariff.diameter_le
    · exact width
    · intro a b
      apply dim
      change dist ((S.maps page).pos (x a)) ((S.maps page).pos (x b)) ≤ _
      have first := reaches a
      rw [dist_comm] at first
      exact (dist_triangle _ (root page.bindW) _).trans (by linarith only [first,reaches b])
  · intro a
    apply dim
    change dist (root page.bindW) ((S.maps page).pos (x a)) ≤ _
    nlinarith only [reaches a,mul_nonneg (add_nonneg hs hd) (S.radius_pos page).le]

end YM.Integration.WilsonIndependentCapturedRootTariff
