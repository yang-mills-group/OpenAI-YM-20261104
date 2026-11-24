import YM.RG.PathActions

/-! The original path rows admit a smaller analytic width without changing
any row or cost. The cap pays the exponential-in-J factors in the full
joint-chart derivative estimate; it does not change the Run's own width. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeCappedPathBounds
open Lattice RG
open scoped Classical BigOperators

private theorem sumBudget_le {ι : Type*} {f g : ι → ℝ} {C : ℝ}
    (h : SumBudget g C) (hf : ∀ i, 0 ≤ f i) (hle : ∀ i, f i ≤ g i) :
    SumBudget f C := by
  have hs : Summable f := h.2.1.of_nonneg_of_le hf hle
  exact ⟨hf, hs, (hs.tsum_le_tsum hle h.2.1).trans h.2.2⟩

/-- Only the analytic width changes; every original summable row is retained. -/
theorem restrict_width {G : Gauge} {W : PathData G} {p : Clip}
    {σ τ C Λ : ℝ} (h : W.Bounds p σ C Λ) (hτ : 0 < τ) (hle : τ ≤ σ) :
    W.Bounds p τ C Λ := by
  have ha {k : ℕ} (a : ℕ → Atom G k) {D : ℝ}
      (hs : SumBudget (fun i => (a i).budget σ) D) :
      SumBudget (fun i => (a i).budget τ) D := by
    apply sumBudget_le hs
    · intro i
      unfold Atom.budget Atom.magnitude
      positivity
    intro i
    unfold Atom.budget
    apply mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)))
    unfold Atom.magnitude
    positivity
  refine { h with
    width := hτ
    rows := ?_
    two := ha W.loop h.two
    three := ha W.cubic h.three
    four := ha W.quartic h.four }
  intro q
  apply sumBudget_le (h.rows q)
  · intro i
    positivity
  intro i
  apply mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)))
    (abs_nonneg _)

/-- The original metric normalization already bounds its direct scalar. -/
theorem direct_le_one {G : Gauge} {W : PathData G} {p : Clip}
    {σ C Λ : ℝ} (h : W.Bounds p σ C Λ) : p.direct ≤ 1 := by
  let q : PlaqAxes := ⟨(0, 1), by decide⟩
  have hm := h.metric q q
  simp at hm
  have hn : 0 ≤ ∑ k, W.symbol0 k q * W.symbol0 k q :=
    Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  linarith

/-- This auxiliary width is used only to estimate derivatives at the same germ. -/
def cappedWidth (σ : ℝ) (j : ℕ) : ℝ := min σ ((j : ℝ) + 3)⁻¹

/-- Its reciprocal costs at most the two original positive scalar inputs. -/
theorem capped_facts {σ : ℝ} (hσ : 0 < σ) (j : ℕ) :
    0 < cappedWidth σ j ∧ cappedWidth σ j ≤ σ ∧
      cappedWidth σ j * ((j : ℝ) + 3) ≤ 1 ∧
      (cappedWidth σ j)⁻¹ ≤ σ⁻¹ + ((j : ℝ) + 3) := by
  have hj : 0 < (j : ℝ) + 3 := by positivity
  refine ⟨lt_min hσ (inv_pos.mpr hj), min_le_left _ _, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hj.le).trans_eq
      (inv_mul_cancel₀ (ne_of_gt hj))
  unfold cappedWidth
  rw [min_def]
  split_ifs with h
  · exact le_add_of_nonneg_right hj.le
  rw [inv_inv]
  exact le_add_of_nonneg_left (inv_nonneg.mpr hσ.le)

end YM.Integration.NativeCappedPathBounds
end
