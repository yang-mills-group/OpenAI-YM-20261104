import YM.IterationFour.Running

namespace YM.Integration.ActualSignedGraphBound
open Filter
open IterationFour.Currency

variable {G : Gauge} {C : Family G}

/-- Iteration of the signed graph remainder (manuscript qdi) on the original
regulator coupling. The same constant works at all admitted periods, top
cutoffs, stopping levels, and for every array with the two stated local
estimates. No monotonicity of the physical coupling is required. -/
theorem uniform (hG : G.Simple) (hC : C.Makes) {s γ A B : ℝ}
    (hs : 0 ≤ s) (hγ : 0 < γ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ K ≥ 0, ∀ (N period stop : ℕ), stop ≤ N → ∀ d : ℕ → ℝ,
      d N ≤ A * g C N period N ^ s →
      (∀ i, stop ≤ i → i < N →
        d i ≤ ((C.S.block i).val : ℝ) ^ (-γ) * d (i + 1) +
          B * g C N period (i + 1) ^ s) →
      d stop ≤ K * g C N period stop ^ s := by
  let q := (3 : ℝ) ^ (-γ)
  let t := (2 : ℝ) ^ s
  let M := max (A * t) (B * t / (1 - q))
  have ht : 0 ≤ t := Real.rpow_nonneg (by norm_num) _
  have hq : 0 < 1 - q := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hγ))
  have hM : 0 ≤ M := (mul_nonneg hA ht).trans (le_max_left _ _)
  have hbudget : q * M + B * t ≤ M := by
    have h := (div_le_iff₀ hq).mp (le_max_right (A * t) (B * t / (1 - q)))
    change B * t ≤ M * (1 - q) at h
    linarith only [h]
  refine ⟨M * t, mul_nonneg hM ht, ?_⟩
  intro N period stop hstop d htop hstep
  let w := weight C.path.levels s
  have hw (i : ℕ) : 0 ≤ w i := (weight_pos C.path.levels i s).le
  have hon (i : ℕ) (hi : i ≤ N) : g C N period i ^ s ≤ t * w i :=
    (g_weight hC hi s hs).2
  have loop : ∀ k i : ℕ, i + k = N → stop ≤ i → d i ≤ M * w i := by
    intro k
    induction k with
    | zero =>
      intro i hi _
      have he : i = N := by omega
      subst i
      calc
        d N ≤ A * g C N period N ^ s := htop
        _ ≤ A * (t * w N) := mul_le_mul_of_nonneg_left (hon N le_rfl) hA
        _ = (A * t) * w N := (mul_assoc _ _ _).symm
        _ ≤ M * w N := mul_le_mul_of_nonneg_right (le_max_left _ _) (hw N)
    | succ k ih =>
      intro i hi hsi
      have hlt : i < N := by omega
      have hnext := ih (i + 1) (by omega) (by omega)
      have hwi : w (i + 1) ≤ w i := across C.path.levels hG hs (Nat.le_succ i)
      have hl : (3 : ℝ) ≤ (C.S.block i).val := by exact_mod_cast C.S.block_large i
      have hqi : ((C.S.block i).val : ℝ) ^ (-γ) ≤ q :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hl (neg_nonpos.mpr hγ.le)
      have hn : d (i + 1) ≤ M * w i := hnext.trans (mul_le_mul_of_nonneg_left hwi hM)
      have hf : g C N period (i + 1) ^ s ≤ t * w i :=
        (hon _ (by omega)).trans (mul_le_mul_of_nonneg_left hwi ht)
      calc
        d i ≤ _ := hstep i hsi hlt
        _ ≤ q * (M * w i) + B * (t * w i) :=
          add_le_add (mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg (by positivity) _)
            |>.trans (mul_le_mul_of_nonneg_right hqi (mul_nonneg hM (hw i))))
            (mul_le_mul_of_nonneg_left hf hB)
        _ = (q * M + B * t) * w i := by ring
        _ ≤ M * w i := mul_le_mul_of_nonneg_right hbudget (hw i)
  calc
    d stop ≤ M * w stop := loop (N - stop) stop (by omega) le_rfl
    _ ≤ M * (t * g C N period stop ^ s) :=
      mul_le_mul_of_nonneg_left (g_weight hC hstop s hs).1 hM
    _ = M * t * g C N period stop ^ s := (mul_assoc _ _ _).symm

/-- A positive order reserve in the one-step and startup estimates pays
every epsilon on one tail, before choosing any regulator or signed array. -/
theorem eventual_small (hG : G.Simple) (hC : C.Makes) {p s γ A B : ℝ}
    (hp : 0 ≤ p) (hps : p < s) (hγ : 0 < γ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ stop : ℕ in atTop, ∀ N period : ℕ, stop ≤ N → ∀ d : ℕ → ℝ,
      d N ≤ A * g C N period N ^ s →
      (∀ i, stop ≤ i → i < N →
        d i ≤ ((C.S.block i).val : ℝ) ^ (-γ) * d (i + 1) +
          B * g C N period (i + 1) ^ s) →
      d stop ≤ ε * g C N period stop ^ p := by
  obtain ⟨K, hK, h⟩ := uniform hG hC (hp.trans hps.le) hγ hA hB
  have h2 : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  filter_upwards [buy C.path.levels hG (K * (2 : ℝ) ^ s)
    (div_pos hε h2) hps] with m hm N period hN d hd hstep
  calc
    d m ≤ K * g C N period m ^ s := h N period m hN d hd hstep
    _ ≤ K * ((2 : ℝ) ^ s * weight C.path.levels s m) :=
      mul_le_mul_of_nonneg_left (g_weight hC hN s (hp.trans hps.le)).2 hK
    _ ≤ (ε / (2 : ℝ) ^ p) * weight C.path.levels p m := by
      rw [← mul_assoc]
      exact hm
    _ ≤ (ε / (2 : ℝ) ^ p) * ((2 : ℝ) ^ p * g C N period m ^ p) :=
      mul_le_mul_of_nonneg_left (g_weight hC hN p hp).1 (div_nonneg hε.le h2.le)
    _ = ε * g C N period m ^ p := by rw [← mul_assoc, div_mul_cancel₀ _ h2.ne']

end YM.Integration.ActualSignedGraphBound
