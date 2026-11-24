import YM.Integration.LocalKernelBlocks
import YM.Integration.LocalComparisonEnvelope

/-! Original analytic-kernel prices on a common represented polynomial.

Complete-polynomial support alone is insufficient here: cancellation can hide
unsupported regular, forced or caption coefficients. `BlockPresentation`
therefore records the exact support of every priced coefficient separately.
With that receipt, the original block product and its single-anchor slot
encoding give literally the same normalized representation, with all roots,
labels, supports and original full-group forced coefficients retained.

The algebraic identity permits zero costs. The `RelativeBudget` corollary
requires positive costs, as does that existing division-based norm; no
zero-cost estimate is inferred from the identity alone.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker RG3.Script.Picnic LocalKernelBlocks
open scoped BigOperators

variable {I V : Type} [DecidableEq I] [DecidableEq V]
    {R : Census V} {G : Gauge} {n : Side} {P : Rep G n}
    {X Y : Type*} {o : V → Site n} (B : Layout I V)

/-- A structural receipt on each coefficient of the fixed presentation,
before choosing independent tests or taking its representation norm. -/
structure BlockPresentation (T : Taste X o P R) : Prop where
  unit v : ¬ B.Admissible (R.fire v).val → ∀ x, T.menu.global x v = 0
  regular i : ¬ B.Admissible (T.menu.rays i).val →
    ∀ x U, T.menu.regular x i U = 0
  forced i j : ¬ B.Admissible (T.menu.marks i j).val →
    ∀ x U, T.menu.force x i j U = 0
  caption i : ¬ B.Admissible (T.tag i).val → ∀ x, T.score x i = 0

theorem BlockPresentation.pullback {T : Taste X o P R}
    (H : BlockPresentation B T) (f : Y → X) :
    BlockPresentation B (pullback f T) where
  unit v h y := H.unit v h (f y)
  regular i h y U := H.regular i h (f y) U
  forced i j h y U := H.forced i j h (f y) U
  caption i h y := H.caption i h (f y)

/-- Agreement only on the supported modes suffices, because the support
receipt concerns the actual priced coefficients, not just their sum. -/
theorem BlockPresentation.priceNormalized_congr {T : Taste X o P R}
    (H : BlockPresentation B T) {cost cost' : R.Mode → ℝ}
    (hc : ∀ q, B.Admissible q.val → cost q = cost' q) :
    priceNormalized cost T = priceNormalized cost' T := by
  have hu : (fun x v => (cost (R.fire v))⁻¹ • T.menu.global x v) =
      fun x v => (cost' (R.fire v))⁻¹ • T.menu.global x v := by
    funext x v
    by_cases h : B.Admissible (R.fire v).val
    · rw [hc _ h]
    · rw [H.unit v h x]
      simp only [smul_zero]
  have hr : (fun x i U => (cost (T.menu.rays i))⁻¹ • T.menu.regular x i U) =
      fun x i U => (cost' (T.menu.rays i))⁻¹ • T.menu.regular x i U := by
    funext x i U
    by_cases h : B.Admissible (T.menu.rays i).val
    · rw [hc _ h]
    · rw [H.regular i h x U]
      simp only [smul_zero]
  have hf : (fun x i j U => (cost (T.menu.marks i j))⁻¹ • T.menu.force x i j U) =
      fun x i j U => (cost' (T.menu.marks i j))⁻¹ • T.menu.force x i j U := by
    funext x i j U
    by_cases h : B.Admissible (T.menu.marks i j).val
    · rw [hc _ h]
    · rw [H.forced i j h x U]
      simp only [smul_zero]
  have ha : (fun x i => (cost (T.tag i))⁻¹ • T.score x i) =
      fun x i => (cost' (T.tag i))⁻¹ • T.score x i := by
    funext x i
    by_cases h : B.Admissible (T.tag i).val
    · rw [hc _ h]
    · rw [H.caption i h x]
      simp only [smul_zero]
  unfold priceNormalized
  rw [hu, hr, hf, ha]

/-- The original block product is paid once per analytic input, even when
that input contains several independent test slots. -/
theorem BlockPresentation.block_priceNormalized [Fintype I]
    {T : Taste X o P R} (H : BlockPresentation B T) (cost : I → ℝ) :
    priceNormalized (fun q => B.blockEnvelope cost q.val) T =
      priceNormalized (envelopeProduct (B.slotCost cost)) T := by
  apply H.priceNormalized_congr
  intro q hq
  exact B.blockEnvelope_eq_slots cost hq

/-- A full original-block relative budget becomes a slot-encoded budget
without changing any regular, forced, mixed, geometric or factorial price. -/
def RelativeBudget.block_to_slots [Fintype I] {T : Taste X o P R}
    {p : BudgetPoint} {w : V → ℝ} {κ a b : ℝ} {cost : I → ℝ}
    (H : RelativeBudget p T w κ (fun q => B.blockEnvelope cost q.val) a b)
    (hs : BlockPresentation B T) (hc : ∀ i, 0 < cost i) :
    RelativeBudget p T w κ (envelopeProduct (B.slotCost cost)) a b where
  positive q := Finset.prod_pos (fun v _ => B.slotCost_positive hc v)
  quiet := by simp [envelopeProduct, Census.quiet]
  budget := by
    rw [← BlockPresentation.block_priceNormalized B hs cost]
    exact H.budget

/-- The same exact identity restores the original input-block convention
after a native supplier has used the single-anchor slot encoding. -/
def RelativeBudget.slots_to_block [Fintype I] {T : Taste X o P R}
    {p : BudgetPoint} {w : V → ℝ} {κ a b : ℝ} {cost : I → ℝ}
    (H : RelativeBudget p T w κ (envelopeProduct (B.slotCost cost)) a b)
    (hs : BlockPresentation B T) (hc : ∀ i, 0 < cost i) :
    RelativeBudget p T w κ (fun q => B.blockEnvelope cost q.val) a b where
  positive q := B.blockEnvelope_positive hc q.val
  quiet := by
    change B.blockEnvelope cost ∅ = 1
    simpa only [B.assemble_empty, Finset.prod_empty] using
      B.blockEnvelope_assemble cost ∅
  budget := by
    rw [BlockPresentation.block_priceNormalized B hs cost]
    exact H.budget

end YM.Integration.LocalComparison
