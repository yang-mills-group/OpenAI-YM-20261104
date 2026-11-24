import YM.Integration.RegulatorWindowRemainder
import Mathlib.Algebra.BigOperators.Intervals

namespace YM.Integration.SignedGraphSoftWindow
open Filter IterationFour.Currency RegulatorWindowRemainder
open scoped BigOperators

variable {G : Gauge} {C : Family G}

/-- The signed boundary transfer uses logarithmic mesh age on the actual schedule. -/
theorem transfer_eq_age (C : Family G) (γ : ℝ) {i top : ℕ} (h : i ≤ top) :
    transfer C γ i top = Real.exp (-γ * (C.S.scale top - C.S.scale i)) := by
  induction top, h using Nat.le_induction with
  | base => simp [transfer]
  | succ top hi ih =>
    have hs : transfer C γ i (top + 1) = transfer C γ i top *
        ((C.S.block top).val : ℝ) ^ (-γ) := Finset.prod_Ico_succ_top hi _
    have hL : 0 < ((C.S.block top).val : ℝ) := Nat.cast_pos.mpr (C.S.block top).property
    rw [hs, ih, Real.rpow_def_of_pos hL, ← Real.exp_add, C.S.scale_succ]
    congr 1
    ring

/-- Every fixed stopping level admits every sufficiently fine upper endpoint
for any prescribed logarithmic window length. -/
theorem eventually_long (C : Family G) {γ : ℝ} (hγ : 0 < γ) (i : ℕ) (r : ℝ) :
    ∀ᶠ top : ℕ in atTop, i ≤ top ∧ r ≤ γ * (C.S.scale top - C.S.scale i) := by
  filter_upwards [eventually_ge_atTop i,
    C.S.divergent.eventually_ge_atTop (r / γ + C.S.scale i)] with top hit hs
  refine ⟨hit, ?_⟩
  have h : r / γ ≤ C.S.scale top - C.S.scale i := by linarith only [hs]
  simpa only [mul_comm] using (div_le_iff₀ hγ).mp h

/-- A polynomially expensive boundary error can be kept on the original
trajectory. Once the true mesh-age window pays its order, the local signed
forcing and this boundary together have order s at the stopping level. -/
theorem polynomial_boundary (hG : G.Simple) (hC : C.Makes) {s t γ A F : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hγ : 0 < γ) (hA : 0 ≤ A) (hF : 0 ≤ F) :
    ∃ K ≥ 0, ∀ (N period i top : ℕ), i ≤ top → top ≤ N →
      (s + t) / 2 * Real.log (B C.path.levels i) ≤ γ * (C.S.scale top - C.S.scale i) →
      ∀ d : ℕ → ℝ, d top ≤ A * g C N period i ^ (-t) →
      (∀ j, i ≤ j → j < top →
        d j ≤ ((C.S.block j).val : ℝ) ^ (-γ) * d (j + 1) +
          F * g C N period (j + 1) ^ s) →
      d i ≤ K * g C N period i ^ s := by
  obtain ⟨k, hk, h⟩ := bounded_forcing hG hC hs hγ hF
  have ht2 : 0 ≤ (2 : ℝ) ^ (s + t) := Real.rpow_nonneg (by norm_num) _
  refine ⟨A * (2 : ℝ) ^ (s + t) + k, add_nonneg (mul_nonneg hA ht2) hk, ?_⟩
  intro N period i top hit htN hage d hd hstep
  have hβ := WardBin.hot C.path.levels i
  have hg := g_pos hC N period i (hit.trans htN)
  have hweight : transfer C γ i top ≤ weight C.path.levels (s + t) i := by
    rw [transfer_eq_age C γ hit]
    change _ ≤ gain (B C.path.levels i) ^ (s + t)
    rw [rpGain _ hβ, Real.rpow_def_of_pos hβ]
    exact Real.exp_le_exp.mpr (by linarith only [hage])
  have hpaid := hweight.trans (g_weight (q := period) hC (hit.trans htN) (s + t) (add_nonneg hs ht)).1
  have htr : 0 ≤ transfer C γ i top := by rw [transfer_eq_age C γ hit]; positivity
  have hb : transfer C γ i top * d top ≤
      A * (2 : ℝ) ^ (s + t) * g C N period i ^ s := by
    calc
      _ ≤ transfer C γ i top * (A * g C N period i ^ (-t)) :=
        mul_le_mul_of_nonneg_left hd htr
      _ ≤ ((2 : ℝ) ^ (s + t) * g C N period i ^ (s + t)) *
            (A * g C N period i ^ (-t)) := mul_le_mul_of_nonneg_right hpaid
          (mul_nonneg hA (Real.rpow_nonneg hg.le _))
      _ = A * (2 : ℝ) ^ (s + t) * (g C N period i ^ (s + t) * g C N period i ^ (-t)) := by ring
      _ = _ := by rw [← Real.rpow_add hg, add_neg_cancel_right]
  calc
    d i ≤ _ := h N period i top hit htN d hstep
    _ ≤ A * (2 : ℝ) ^ (s + t) * g C N period i ^ s + k * g C N period i ^ s :=
      add_le_add hb le_rfl
    _ = _ := (add_mul _ _ _).symm

/-- With positive order reserve, every late stopping level and all sufficiently
fine upper endpoints give the required physical little-o estimate. The same
choice precedes every regulator beyond that endpoint and every signed array. -/
theorem eventual_small (hG : G.Simple) (hC : C.Makes) {p s t γ A F ε : ℝ}
    (hp : 0 ≤ p) (hps : p < s) (ht : 0 ≤ t) (hγ : 0 < γ)
    (hA : 0 ≤ A) (hF : 0 ≤ F) (hε : 0 < ε) :
    ∀ᶠ i : ℕ in atTop, ∀ᶠ top : ℕ in atTop, ∀ (N period : ℕ), top ≤ N →
      ∀ d : ℕ → ℝ, d top ≤ A * g C N period i ^ (-t) →
      (∀ j, i ≤ j → j < top →
        d j ≤ ((C.S.block j).val : ℝ) ^ (-γ) * d (j + 1) +
          F * g C N period (j + 1) ^ s) →
      d i ≤ ε * g C N period i ^ p := by
  have hs := hp.trans hps.le
  obtain ⟨K, hK, hbound⟩ := polynomial_boundary hG hC hs ht hγ hA hF
  have h2 : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  filter_upwards [buy C.path.levels hG (K * (2 : ℝ) ^ s) (div_pos hε h2) hps] with i hi
  filter_upwards [eventually_long C hγ i ((s + t) / 2 * Real.log (B C.path.levels i))]
    with top htop N period htN d hd hstep
  have hiN := htop.1.trans htN
  calc
    d i ≤ K * g C N period i ^ s := hbound N period i top htop.1 htN htop.2 d hd hstep
    _ ≤ K * ((2 : ℝ) ^ s * weight C.path.levels s i) :=
      mul_le_mul_of_nonneg_left (g_weight hC hiN s hs).2 hK
    _ ≤ (ε / (2 : ℝ) ^ p) * weight C.path.levels p i := by
      rwa [← mul_assoc]
    _ ≤ (ε / (2 : ℝ) ^ p) * ((2 : ℝ) ^ p * g C N period i ^ p) :=
      mul_le_mul_of_nonneg_left (g_weight hC hiN p hp).1 (div_nonneg hε.le h2.le)
    _ = ε * g C N period i ^ p := by rw [← mul_assoc, div_mul_cancel₀ _ h2.ne']

end YM.Integration.SignedGraphSoftWindow
