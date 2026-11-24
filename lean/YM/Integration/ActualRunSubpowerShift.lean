import YM.Integration.FullQLocalNumericSchedule
import YM.Integration.ActualRunAdjacentHatBeta
import YM.IterationFour.Running

/-! A fixed shift preserves the original Run's uniform subpower tail.
The proof keeps every target cutoff and period, including N=m+1. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunSubpowerShift
open Filter RG FullQLocal FullQLocal.RenderedStep
open PhysicalNext.Repeat.Legato
open scoped Topology

variable {G : Gauge}

/-- A scalar family is subpower at every representation of the next input level. -/
def Subpower (R : Run G) (f : ℕ → ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      f m ≤ Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^ (-epsilon)

private theorem power_small (R : Run G) (hG : G.Simple)
    (C : ℝ) (hC : 0 ≤ C) (s : ℝ) (hs : 0 < s) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      C * Pert.Asymptotics.regulatorRun R.family N period (m + 1) ^ s ≤ 1 := by
  have hf : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨start, hstart⟩ := eventually_atTop.1
    (IterationFour.Currency.buy R.family.path.levels hG C
      (k := ((2 : ℝ) ^ s)⁻¹) (inv_pos.mpr hf) (s := 0) (t := s) hs)
  filter_upwards [eventually_ge_atTop start] with m hm N period hN
  let g := Pert.Asymptotics.regulatorRun R.family N period (m + 1)
  have hp : C * IterationFour.Currency.weight R.family.path.levels s (m + 1) ≤
      ((2 : ℝ) ^ s)⁻¹ := by
    simpa only [IterationFour.Currency.weight, Real.rpow_zero, mul_one] using
      hstart (m + 1) (by omega)
  calc
    C * g ^ s ≤ C * ((2 : ℝ) ^ s *
        IterationFour.Currency.weight R.family.path.levels s (m + 1)) :=
      mul_le_mul_of_nonneg_left
        (IterationFour.Currency.g_weight R.makes
          (N := N) (q := period) (i := m + 1) (by omega) s hs.le).2 hC
    _ = (2 : ℝ) ^ s *
        (C * IterationFour.Currency.weight R.family.path.levels s (m + 1)) := by ring
    _ ≤ (2 : ℝ) ^ s * ((2 : ℝ) ^ s)⁻¹ :=
      mul_le_mul_of_nonneg_left hp hf.le
    _ = 1 := mul_inv_cancel₀ hf.ne'

private theorem reference_regulator (R : Run G) (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      Pert.Asymptotics.regulatorRun R.family N period (m + 1) ≤
        3 * Pert.Asymptotics.regulatorRun R.family (m + 2) 0 (m + 2) := by
  obtain ⟨start, hstart⟩ := eventually_atTop.1
    (ActualRunAdjacentHatBeta.three_halves R hG)
  filter_upwards [eventually_ge_atTop start] with m hm N period hN
  have hnext := hstart (m + 1) (by omega)
  change R.family.path.levels.clock.hatBeta (m + 2) ≤
    (3 / 2 : ℝ) * R.family.path.levels.clock.hatBeta (m + 1) at hnext
  have hconv := R.makes.wilson.represents N period (m + 1) (by omega)
  have hconv0 := R.makes.wilson.represents (m + 2) 0 (m + 2) le_rfl
  let b := R.family.path.β N period (m + 1)
  let b0 := R.family.path.β (m + 2) 0 (m + 2)
  have hlo : R.family.path.levels.clock.hatBeta (m + 1) / 2 ≤ b := hconv.band.1
  have hhi : b0 ≤ 2 * R.family.path.levels.clock.hatBeta (m + 2) := hconv0.band.2
  have hb : 0 < b := by
    have hh := R.family.path.levels.fits.delayed (m + 1)
    linarith
  have hb0 : 0 < b0 := by
    have hh := R.family.path.levels.fits.delayed (m + 2)
    have hlow := hconv0.band.1
    change R.family.path.levels.clock.hatBeta (m + 2) / 2 ≤ b0 at hlow
    linarith
  have hbound : b0 ≤ (9 : ℝ) * b := by
    nlinarith only [hlo, hhi, hnext, hb]
  have hsqrt : Real.sqrt b0 ≤ 3 * Real.sqrt b := by
    have h9 : Real.sqrt (9 : ℝ) = 3 := by norm_num
    simpa only [Real.sqrt_mul (x := 9) (by norm_num : (0 : ℝ) ≤ 9), h9] using
      Real.sqrt_le_sqrt hbound
  have hdiv : 1 / Real.sqrt b ≤ 3 / Real.sqrt b0 :=
    (div_le_div_iff₀ (Real.sqrt_pos.mpr hb) (Real.sqrt_pos.mpr hb0)).mpr
      (by simpa only [one_mul] using hsqrt)
  change (Real.sqrt b)⁻¹ ≤ 3 * (Real.sqrt b0)⁻¹
  simpa only [div_eq_mul_inv, one_mul] using hdiv

/-- One fixed forward shift preserves the full actual subpower tail. -/
theorem shift_one (R : Run G) (hG : G.Simple) (f : ℕ → ℝ)
    (hf : ∀ m, 0 ≤ f m) (hsub : Subpower R f) :
    Subpower R (fun m => f (m + 1)) := by
  intro epsilon hepsilon
  let d := epsilon / 2
  have hd : 0 < d := half_pos hepsilon
  obtain ⟨start, hstart⟩ := eventually_atTop.1 (hsub d hd)
  filter_upwards [reference_regulator R hG,
    power_small R hG ((3 : ℝ) ^ d) (Real.rpow_nonneg (by norm_num) _) d hd,
    eventually_ge_atTop start] with m href hsmall hm N period hN
  let g := Pert.Asymptotics.regulatorRun R.family N period (m + 1)
  let g0 := Pert.Asymptotics.regulatorRun R.family (m + 2) 0 (m + 2)
  have hg : 0 < g := IterationFour.Currency.g_pos R.makes N period (m + 1) (by omega)
  have hg0 : 0 < g0 := IterationFour.Currency.g_pos R.makes (m + 2) 0 (m + 2) le_rfl
  have hk : f (m + 1) ≤ g0 ^ (-d) :=
    hstart (m + 1) (by omega) (m + 2) 0 (by omega)
  have hpaid0 : f (m + 1) * g0 ^ d ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hg0.le d)
    simpa only [← Real.rpow_add hg0, neg_add_cancel, Real.rpow_zero] using h
  have hp : g ^ d ≤ (3 : ℝ) ^ d * g0 ^ d := by
    calc
      g ^ d ≤ (3 * g0) ^ d := Real.rpow_le_rpow hg.le (href N period hN) hd.le
      _ = (3 : ℝ) ^ d * g0 ^ d := Real.mul_rpow (by norm_num) hg0.le
  have hpaid : f (m + 1) * g ^ d ≤ (3 : ℝ) ^ d := by
    calc
      _ ≤ f (m + 1) * ((3 : ℝ) ^ d * g0 ^ d) :=
        mul_le_mul_of_nonneg_left hp (hf (m + 1))
      _ = (3 : ℝ) ^ d * (f (m + 1) * g0 ^ d) := by ring
      _ ≤ (3 : ℝ) ^ d * 1 :=
        mul_le_mul_of_nonneg_left hpaid0 (Real.rpow_nonneg (by norm_num) _)
      _ = (3 : ℝ) ^ d := mul_one _
  have hpaidFull : f (m + 1) * g ^ epsilon ≤ 1 := by
    calc
      _ = (f (m + 1) * g ^ d) * g ^ d := by
        rw [show epsilon = d + d by dsimp [d]; ring, Real.rpow_add hg]
        ring
      _ ≤ (3 : ℝ) ^ d * g ^ d :=
        mul_le_mul_of_nonneg_right hpaid (Real.rpow_nonneg hg.le d)
      _ ≤ 1 := hsmall N period hN
  change f (m + 1) ≤ g ^ (-epsilon)
  rw [Real.rpow_neg hg.le, ← one_div]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hg epsilon)).mpr hpaidFull

/-- Every fixed finite shift is chosen before the common tail; all later
cutoffs and periods remain arbitrary. -/
theorem fixed_shift (R : Run G) (hG : G.Simple) (f : ℕ → ℝ)
    (hf : ∀ m, 0 ≤ f m) (hsub : Subpower R f) (k : ℕ) :
    Subpower R (fun m => f (m + k)) := by
  induction k with
  | zero => exact hsub
  | succ k ih =>
      have hstep := shift_one R hG (fun m => f (m + k))
        (fun m => hf (m + k)) ih
      have hfun : (fun m => f ((m + 1) + k)) =
          (fun m => f (m + (k + 1))) := by
        funext m
        exact congrArg f (by omega)
      exact Eq.mp (congrArg (Subpower R) hfun) hstep

end YM.Integration.ActualRunSubpowerShift
end
