import YM.IterationFour.Vacuum.Reclose
import YM.IterationFour.Vacuum.Render

/-!
The literal pre-reset representation, before affine extraction. Original forced
addresses, predicates, and values are unchanged. The added low/high rows retain
the native orientation average and masks. All series identities use summability;
no affine-null `Activities.Valid` is required of the raw representation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.LocalComparison.PreReset
open Function Lattice Wilson RG
open AnalyticBridge VerifiedReset Collection Quotes
open IterationFour.Vacuum Extra.Iteration
open scoped BigOperators
variable {G : Gauge} {n : Side}

def labels (W : PathData G) (p : BudgetPoint) (X : Listing G n) :
    EKey n → RegularAddress n :=
  Sum.elim X.reg (Sum.elim (lowEntry G W p) (highEntry G W))

def rows (W : PathData G) (c : Clip) (v : Collection.Source G n) (α : ℝ) :
    EKey n → Pot G n :=
  Sum.elim v.logRead (Sum.elim
    (fun i U => (α * factor) * (i.2.mark W c * i.2.plain W 0 (i.1.view U)))
    (fun i U => (α * factor) * i.2.plain W 0 (i.1.view U)))

def activities (W : PathData G) (c : Clip) (p : BudgetPoint)
    (X : Listing G n) (v : Collection.Source G n) (α : ℝ) : Activities G n :=
  ⟨labels W p X ∘ numbering (EKey n), X.hard,
    rows W c v α ∘ numbering (EKey n), v.hardRead⟩

def rep (W : PathData G) (c : Clip) (p : BudgetPoint)
    (X : Listing G n) (v : Collection.Source G n) (β τ α : ℝ) : RG.Rep G n :=
  ⟨W, c, activities W c p X v α, p, β, τ⟩

def append (S : List (Piece G n)) (W : PathData G) (c : Clip) (p : BudgetPoint)
    (X : Listing G n) (v : Collection.Source G n) (β τ α : ℝ)
    (k : Piece G n → ℝ) : RG.Rep G n :=
  Render.append S (rep W c p X v β τ α) k

/-- A finite regular budget suffices for summability, without flat/affine nullness. -/
lemma series_of_EBound {A : Activities G n} {p : BudgetPoint} {b : ℝ}
    (h : A.EBound p b) (U : Config G n) : Summable (fun i => A.regularOccurrence p i U) := by
  obtain ⟨q,hq,hb⟩ := Activities.E_total h
  apply Summable.of_norm
  apply hq.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_)
  by_cases he : Healthy p.threshold (A.reg i).support U
  · rw [Activities.regularOccurrence, masked_eq _ _ _ _ he]
    exact (hb i).2 U he [] (Nat.zero_le _) (by simp)
  · rw [Activities.regularOccurrence, masked_ne _ _ _ _ he, norm_zero]
    exact (hb i).1

lemma payload_series {P : Payload G n} {p : BudgetPoint} {b : ℝ}
    (h : P.Invoice p b) (A : Activities G n) (U : Config G n) :
    Summable (fun i => masked p.threshold (P.labels i).support (P.action i) U) := by
  let B : Activities G n := { A with reg := P.labels, E := P.action }
  exact series_of_EBound (A := B) h.credit U

private def piece (W : PathData G) (c : Clip) (p : BudgetPoint)
    (X : Listing G n) (v : Collection.Source G n) (α : ℝ) (U : Config G n)
    (i : EKey n) : ℝ :=
  masked p.threshold (labels W p X i).support (rows W c v α i) U

private lemma piece_low (W : PathData G) (c : Clip) (p : BudgetPoint)
    (X : Listing G n) (v : Collection.Source G n) (α : ℝ) (U : Config G n)
    (i : Faces n) : piece W c p X v α U (.inr (.inl i)) =
      α * stack (fun d : Low => d.maskedPlain W c 0 p) U i := by
  change masked p.threshold (i.1.spread (i.2.home W p 0))
    ((fun V => (α * factor) * (i.2.mark W c * i.2.plain W 0 V)) ∘ i.1.view) U = _
  rw [Seat.distribute, comp_apply, mask_mul]
  unfold stack Low.maskedPlain
  ring

private lemma piece_high (W : PathData G) (c : Clip) (p : BudgetPoint)
    (X : Listing G n) (v : Collection.Source G n) (α : ℝ) (U : Config G n)
    (i : Spikes n) : piece W c p X v α U (.inr (.inr i)) =
      α * stack (fun d : High => summit W p d 0) U i := by
  change masked p.threshold (i.1.spread (i.2.home W 0))
    ((fun V => (α * factor) * i.2.plain W 0 V) ∘ i.1.view) U = _
  rw [Seat.distribute, comp_apply, mask_mul]
  unfold stack summit
  ring

private lemma piece_low_total (W : PathData G) (c : Clip) (p : BudgetPoint)
    (X : Listing G n) (v : Collection.Source G n) (α : ℝ)
    (h : ∀ U : Config G n, Summable (fun d : Low => d.maskedPlain W c (0 : Site n) p U))
    (U : Config G n) :
    (∑' i : Faces n, piece W c p X v α U (.inr (.inl i))) = α * receipt W c p U := by
  calc
    _ = ∑' i : Faces n, α * stack (fun d : Low => d.maskedPlain W c (0 : Site n) p) U i :=
      tsum_congr (piece_low W c p X v α U)
    _ = α * (∑' i : Faces n, stack (fun d : Low => d.maskedPlain W c (0 : Site n) p) U i) := by
      rw [tsum_mul_left]
    _ = α * receipt W c p U :=
      congrArg (fun x : ℝ => α * x)
        (layer_total (fun d : Low => d.maskedPlain W c (0 : Site n) p) U h).symm

private lemma piece_high_total (W : PathData G) (c : Clip) (p : BudgetPoint)
    (X : Listing G n) (v : Collection.Source G n) (α : ℝ)
    (h : ∀ U : Config G n, Summable (fun d : High => summit W p d (0 : Site n) U))
    (U : Config G n) :
    (∑' i : Spikes n, piece W c p X v α U (.inr (.inr i))) = α * Reset.leading W p U := by
  calc
    _ = ∑' i : Spikes n, α * stack (fun d : High => summit W p d (0 : Site n)) U i :=
      tsum_congr (piece_high W c p X v α U)
    _ = α * (∑' i : Spikes n, stack (fun d : High => summit W p d (0 : Site n)) U i) := by
      rw [tsum_mul_left]
    _ = α * Reset.leading W p U :=
      congrArg (fun x : ℝ => α * x)
        (layer_total (fun d : High => summit W p d (0 : Site n)) U h).symm

set_option maxHeartbeats 800000 in
lemma raw_series_additive (W : PathData G) (c : Clip) (p : BudgetPoint)
    (X : Listing G n) (v : Collection.Source G n) (α : ℝ)
    (hX : ∀ U, Summable (fun i => (X.read v).regularOccurrence p i U))
    (hLow : ∀ U : Config G n, Summable (fun d : Low => d.maskedPlain W c (0 : Site n) p U))
    (hHigh : ∀ U : Config G n, Summable (fun d : High => summit W p d (0 : Site n) U))
    (U : Config G n) :
    Summable (fun i => (activities W c p X v α).regularOccurrence p i U) ∧
      (activities W c p X v α).additive p U =
        (X.read v).additive p U + α * receipt W c p U + α * Reset.leading W p U := by
  let f := piece W c p X v α U
  let N := numbering (EKey n)
  have h0 : Summable (fun i => f (.inl i)) := hX U
  have h1 : Summable (fun i : Faces n => f (.inr (.inl i))) :=
    ((stack_series _ U hLow).mul_left α).congr (fun i => (piece_low W c p X v α U i).symm)
  have h2 : Summable (fun i : Spikes n => f (.inr (.inr i))) :=
    ((stack_series _ U hHigh).mul_left α).congr (fun i => (piece_high W c p X v α U i).symm)
  have hs : Summable f := Summable.sum _ h0 (Summable.sum _ h1 h2)
  refine ⟨hs.comp_injective N.injective, ?_⟩
  change (∑' i, f (N i)) = _
  rw [N.tsum_eq f, Summable.tsum_sum (f := f) h0 (Summable.sum _ h1 h2),
    Summable.tsum_sum (f := fun i => f (.inr i)) h1 h2]
  change (X.read v).additive p U +
    ((∑' i : Faces n, piece W c p X v α U (.inr (.inl i))) +
      (∑' i : Spikes n, piece W c p X v α U (.inr (.inr i)))) = _
  rw [piece_low_total W c p X v α hLow U, piece_high_total W c p X v α hHigh U]
  exact (add_assoc _ _ _).symm

lemma rep_eval (W : PathData G) (c : Clip) (p : BudgetPoint)
    (X : Listing G n) (v : Collection.Source G n) (β τ α : ℝ)
    (hX : ∀ U, Summable (fun i => (X.read v).regularOccurrence p i U))
    (hLow : ∀ U : Config G n, Summable (fun d : Low => d.maskedPlain W c (0 : Site n) p U))
    (hHigh : ∀ U : Config G n, Summable (fun d : High => summit W p d (0 : Site n) U)) (U : Config G n) :
    (rep W c p X v β τ α).eval U = Reset.supplied W c p X v β τ α U := by
  have he : (rep W c p X v β τ α).exponent U = (frozen X W c p v β τ).exponent U +
      (-α * receipt W c p U) + (-α * Reset.leading W p U) := by
    change τ * _ - W.inChannels c p β U - (activities W c p X v α).additive p U = _
    rw [(raw_series_additive W c p X v α hX hLow hHigh U).2]
    unfold Rep.exponent frozen
    ring
  unfold Reset.supplied earlyValue
  rw [Rep.eval, he, Real.exp_add, Real.exp_add, Rep.eval]
  change _ * (X.read v).gas p U = _
  dsimp only [frozen]
  ring

set_option maxHeartbeats 800000 in
private lemma attach_series_additive (P : Payload G n) (A : Activities G n)
    (p : BudgetPoint) (k : ℝ) (U : Config G n)
    (hA : Summable (fun i => A.regularOccurrence p i U))
    (hP : Summable (fun i => masked p.threshold (P.labels i).support (P.action i) U)) :
    Summable (fun i => (P.attach k A).regularOccurrence p i U) ∧
      (P.attach k A).additive p U = A.additive p U + k * P.amount p U := by
  let f (i : ℕ ⊕ ℕ) := (P.attach k A).regularOccurrence p (Payload.coding.symm i) U
  have h0 (i : ℕ) : f (.inl i) = A.regularOccurrence p i U := by
    simp only [f, Activities.regularOccurrence, Payload.attach, comp_apply,
      Equiv.apply_symm_apply, Sum.elim_inl]
  have h1 (i : ℕ) : f (.inr i) = k * masked p.threshold (P.labels i).support (P.action i) U := by
    simp only [f, Activities.regularOccurrence, Payload.attach, comp_apply,
      Equiv.apply_symm_apply, Sum.elim_inr, Pi.smul_apply]
    by_cases hv : Healthy p.threshold (P.labels i).support U <;> simp [hv]
  have hs0 : Summable (fun i => f (.inl i)) := hA.congr (fun i => (h0 i).symm)
  have hs1 : Summable (fun i => f (.inr i)) := (hP.mul_left k).congr (fun i => (h1 i).symm)
  have hs : Summable f := Summable.sum _ hs0 hs1
  have hi i : (P.attach k A).regularOccurrence p i U = f (Payload.coding i) := by
    simp only [f, Equiv.symm_apply_apply]
  constructor
  · exact (hs.comp_injective Payload.coding.injective).congr (fun i => (hi i).symm)
  change (∑' i, (P.attach k A).regularOccurrence p i U) = _
  simp_rw [hi]
  rw [Payload.coding.tsum_eq f, Summable.tsum_sum hs0 hs1]
  simp_rw [h0, h1]
  rw [tsum_mul_left]
  rfl

lemma append_eval_of_series (S : List (Piece G n)) (R : Rep G n) (k : Piece G n → ℝ)
    (hR : ∀ U, Summable (fun i => R.activities.regularOccurrence R.p i U))
    (hS : ∀ w ∈ S, ∀ U, Summable (fun i => masked R.p.threshold (w.packet.labels i).support (w.packet.action i) U))
    (U : Config G n) : (Render.append S R k).eval U =
      R.eval U * Real.exp (-Render.renders k R.p U S) := by
  have hsum : Summable (fun i => (Render.adorn k R.activities S).regularOccurrence R.p i U) ∧
      (Render.adorn k R.activities S).additive R.p U =
        R.activities.additive R.p U + Render.renders k R.p U S := by
    induction S with
    | nil => exact ⟨hR U, by simp [Render.adorn, Render.renders]⟩
    | cons w l ih =>
      have ht := ih (fun s hs => hS s (List.mem_cons_of_mem w hs))
      have hp := attach_series_additive w.packet (Render.adorn k R.activities l) R.p (k w) U
        ht.1 (hS w List.mem_cons_self U)
      refine ⟨hp.1, ?_⟩
      change (w.packet.attach (k w) (Render.adorn k R.activities l)).additive R.p U = _
      rw [hp.2, ht.2, Render.renders]
      ring
  have he : (Render.append S R k).exponent U = R.exponent U - Render.renders k R.p U S := by
    change R.v * _ - R.path.inChannels R.clip R.p R.beta U -
      (Render.adorn k R.activities S).additive R.p U = _
    rw [hsum.2]
    unfold Rep.exponent
    ring
  rw [Rep.eval, he, sub_eq_add_neg, Real.exp_add, Rep.eval]
  change _ * (Render.adorn k R.activities S).gas R.p U = _
  rw [Render.gas]
  ring

/-- Complete raw representation with the same full gas and all model layers. -/
lemma append_eval (S : List (Piece G n)) (W : PathData G) (c : Clip) (p : BudgetPoint)
    (X : Listing G n) (v : Collection.Source G n) (β τ α : ℝ) (k : Piece G n → ℝ)
    {σ C Λ : ℝ} (hW : W.Bounds c σ C Λ)
    (hX : ∀ U, Summable (fun i => (X.read v).regularOccurrence p i U))
    (hS : ∀ w ∈ S, ∀ U, Summable (fun i => masked p.threshold (w.packet.labels i).support (w.packet.action i) U))
    (U : Config G n) :
    (append S W c p X v β τ α k).eval U =
      Reset.supplied W c p X v β τ α U * Real.exp (-Render.renders k p U S) := by
  have hl := fun U : Config G n => Low.maskedPlain_sum hW p (0 : Site n) U
  have hh := fun U : Config G n => summit_sum hW p U (0 : Site n)
  rw [append, append_eval_of_series S (rep W c p X v β τ α) k
    (fun U => (raw_series_additive W c p X v α hX hl hh U).1) hS U,
    rep_eval W c p X v β τ α hX hl hh U]
  rfl

end YM.Integration.LocalComparison.PreReset
