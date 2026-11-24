import YM.Integration.ActualSignedGraphBound

namespace YM.Integration.RegulatorWindowRemainder

open Filter IterationFour.Currency
open scoped BigOperators

variable {G : Gauge} {C : Family G}

/-- The inherited signed graph contribution uses every block of the chosen
regulator window, in its original order of descent. -/
noncomputable def transfer (C : Family G) (γ : ℝ) (i top : ℕ) : ℝ :=
  ∏ j ∈ Finset.Ico i top, ((C.S.block j).val : ℝ) ^ (-γ)

/-- An arbitrary boundary value at a chosen fine level propagates with the
exact product of block contractions. The forcing constant works uniformly on
every subwindow of the same physical regulator, including an empty window. -/
theorem bounded_forcing (hG : G.Simple) (hC : C.Makes) {s γ B : ℝ}
    (hs : 0 ≤ s) (hγ : 0 < γ) (hB : 0 ≤ B) :
    ∃ K ≥ 0, ∀ (N period stop top : ℕ), stop ≤ top → top ≤ N → ∀ d : ℕ → ℝ,
      (∀ i, stop ≤ i → i < top →
        d i ≤ ((C.S.block i).val : ℝ) ^ (-γ) * d (i + 1) +
          B * g C N period (i + 1) ^ s) →
      d stop ≤ transfer C γ stop top * d top + K * g C N period stop ^ s := by
  obtain ⟨K, hK, h⟩ := ActualSignedGraphBound.uniform hG hC hs hγ
    (le_refl (0 : ℝ)) hB
  refine ⟨K, hK, ?_⟩
  intro N period stop top hst htN d hstep
  let z (i : ℕ) : ℝ := if i < top then d i - transfer C γ i top * d top else 0
  have hz (i : ℕ) (hi : i ≤ top) : z i = d i - transfer C γ i top * d top := by
    rcases lt_or_eq_of_le hi with hl | rfl
    · simp only [z, if_pos hl]
    · simp [z, transfer]
  have hzN : z N ≤ 0 * g C N period N ^ s := by
    simp [z, not_lt.mpr htN]
  have hzstep (i : ℕ) (hsi : stop ≤ i) (hiN : i < N) :
      z i ≤ ((C.S.block i).val : ℝ) ^ (-γ) * z (i + 1) +
        B * g C N period (i + 1) ^ s := by
    by_cases hit : i < top
    · rw [hz i hit.le, hz (i + 1) hit]
      have hsplit : transfer C γ i top =
          ((C.S.block i).val : ℝ) ^ (-γ) * transfer C γ (i + 1) top :=
        Finset.prod_eq_prod_Ico_succ_bot hit _
      rw [hsplit, mul_sub]
      linarith only [hstep i hsi hit]
    · have his : ¬ i + 1 < top := by omega
      simp only [z, if_neg hit, if_neg his, mul_zero, zero_add]
      exact mul_nonneg hB (Real.rpow_nonneg (g_pos hC N period (i + 1) hiN).le _)
  have hend := h N period stop (hst.trans htN) z hzN hzstep
  rw [hz stop hst] at hend
  linarith only [hend]

/-- The exact boundary multiplier has geometric decay in the number of
removed levels, uniformly over the block sequence. -/
theorem transfer_le (C : Family G) {γ : ℝ} (hγ : 0 ≤ γ) (i top : ℕ) :
    transfer C γ i top ≤ ((3 : ℝ) ^ (-γ)) ^ (top - i) := by
  unfold transfer
  calc
    _ ≤ ∏ j ∈ Finset.Ico i top, (3 : ℝ) ^ (-γ) := by
      apply Finset.prod_le_prod
      · intro j _
        exact Real.rpow_nonneg (by positivity) _
      · intro j _
        exact Real.rpow_le_rpow_of_nonpos (by norm_num)
          (show (3 : ℝ) ≤ (C.S.block j).val by exact_mod_cast C.S.block_large j)
          (neg_nonpos.mpr hγ)
    _ = _ := by simp

end YM.Integration.RegulatorWindowRemainder
