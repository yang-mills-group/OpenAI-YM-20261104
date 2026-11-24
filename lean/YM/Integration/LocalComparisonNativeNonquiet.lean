import YM.Integration.LocalComparisonRelativeRows

/-!
The original quiet K is a background reserve, not part of the small marked
error. The common marked payment controls every nonquiet coefficient of the
literal full barcode. The final identity puts back exactly that same quiet
profile and retains all of its compulsory-cover partners.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay
open RG3.Forms RG3.Script.Picnic MergeProof MergeProof.Accent Push Push.AbsoluteSums
open scoped BigOperators Classical

private theorem tally_fst {Y V : Type*} [DecidableEq V] {R : Census V}
    (F : ℕ × ℕ → Y → Poly R) (i : ℕ) (y : Y) :
    tally Prod.fst F i y = ∑' j, F (i, j) y := by
  let e : ℕ ≃ {p : ℕ × ℕ // p.1 = i} := {
    toFun := fun j => ⟨(i, j), rfl⟩
    invFun := fun p => p.val.2
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨⟨k, j⟩, h⟩
      cases h
      rfl }
  exact (e.tsum_eq (fun p => F p.val y)).symm

variable {G : Gauge} {n : Side} {V : Type} {X : Type*}
    [Fintype V] [DecidableEq V] {R : Census V} {P : Rep G n}
    {o : V → Site n} {T : Taste X o P R} {p : BudgetPoint}
    {w cost : V → ℝ} {κ regularPrice forcedPrice : ℝ}

/-- All nonempty marked modes have a common small payment. The quiet
reserve is used only to justify the literal original countable sum. -/
theorem FullBudget.native_nonquiet
    (h : FullBudget p T w κ regularPrice forcedPrice)
    {quietPoint : BudgetPoint} {quietPrice : ℝ}
    (hK : P.activities.KBound quietPoint quietPrice) (x₀ : X) :
    Towed w Prod.fst
      (fun box (z : X × Config G n) => Poly.inject (fun q =>
        if q = R.quiet then 0 else
          (OverlayForcedBarcode.full (T.leaf z.1).contents box z.2).part q))
      p.B p.supportExponent (Fintype.card V * (κ * forcedPrice)) := by
  have hm := towing (r := fun i : ℕ => (P.activities.forced i).support)
    Prod.fst (fun i (z : X × Config G n) => (T.leaf z.1).contents.tagged i.1 i.2 z.2)
    (h.native_marked x₀) h.radii
  have he : tally Prod.fst
      (fun i (z : X × Config G n) => (T.leaf z.1).contents.tagged i.1 i.2 z.2) =
      (fun i (z : X × Config G n) => ∑' j, (T.leaf z.1).contents.tagged i j z.2) := by
    funext i z
    exact tally_fst _ i z
  rw [he] at hm
  have hquiet := native_quiet (R := R) (X := X) (w := w) hK
  have hpart (z : X × Config G n) (box : Box n) (q : R.Mode) (hq : q ≠ R.quiet) :
      (OverlayForcedBarcode.full (T.leaf z.1).contents box z.2).part q =
      (tally (barcode P.activities)
        (fun i (y : X × Config G n) => ∑' j, (T.leaf y.1).contents.tagged i j y.2) box z).part q := by
    have hsum : Summable (fun i => (T.leaf z.1).contents.each i z.2) := by
      exact ((hquiet.repair h.radii z).2).add ((hm.repair h.radii z).2)
    have hfull : Summable (fun i : {i : ℕ // barcode P.activities i = box} =>
        (T.leaf z.1).contents.each i.val z.2) :=
      hsum.comp_injective Subtype.val_injective
    have hmarked : Summable (fun i : {i : ℕ // barcode P.activities i = box} =>
        ∑' j, (T.leaf z.1).contents.tagged i.val j z.2) :=
      (hm.repair h.radii z).2.comp_injective Subtype.val_injective
    unfold OverlayForcedBarcode.full tally
    rw [Poly.share hfull, Poly.share hmarked]
    apply tsum_congr
    intro i
    simp only [Overlay.Bands.each, Poly.part_plus, Poly.part_send, if_neg hq, zero_add]
  have hb := towing (r := Prod.fst) (barcode P.activities)
    (fun i (z : X × Config G n) => ∑' j, (T.leaf z.1).contents.tagged i j z.2) hm h.radii
  obtain ⟨a, ha, hHit, hLoci⟩ := hb
  refine ⟨a, ha, hHit, ?_⟩
  intro box
  obtain ⟨b, hb, hbound, hprice⟩ := hLoci box
  refine ⟨b, hb, ?_, hprice⟩
  intro z q
  change ‖if q = R.quiet then 0 else _‖ ≤ b q
  by_cases hq : q = R.quiet
  · rw [if_pos hq, norm_zero]
    exact hb q
  · rw [if_neg hq, hpart z box q hq]
    exact hbound z q

/-- Original kernel radii are restored without adding the quiet background
to the marked error bill. The envelope still precedes every test and field. -/
theorem RelativeBudget.native_nonquiet
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) {quietPoint : BudgetPoint} {quietPrice : ℝ}
    (hK : P.activities.KBound quietPoint quietPrice) (x₀ : X) :
    Towed (relativeRadii w cost) Prod.fst
      (fun box (z : X × Config G n) => Poly.inject (fun q =>
        if q = R.quiet then 0 else
          (OverlayForcedBarcode.full (T.leaf z.1).contents box z.2).part q))
      p.B p.supportExponent (Fintype.card V * (κ * forcedPrice)) := by
  have ht := towed_restoreEnvelope cost hc (h.budget.native_nonquiet hK x₀)
  have he :
      (fun box (z : X × Config G n) =>
        restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)
          (Poly.inject (fun q => if q = R.quiet then 0 else
            (OverlayForcedBarcode.full
              ((priceNormalized (envelopeProduct cost) T).leaf z.1).contents box z.2).part q))) =
      (fun box (z : X × Config G n) => Poly.inject (fun q =>
        if q = R.quiet then 0 else
          (OverlayForcedBarcode.full (T.leaf z.1).contents box z.2).part q)) := by
    funext box z
    apply Marker.Poly.ext
    intro q
    change (envelopeProduct cost q : ℂ) * (if q = R.quiet then 0 else _) =
      if q = R.quiet then 0 else _
    by_cases hq : q = R.quiet
    · rw [if_pos hq, if_pos hq, mul_zero]
    · rw [if_neg hq, if_neg hq]
      exact congrArg (fun A : Poly R => A.part q) (restore_full_forced hc z.1 box z.2)
  rwa [he] at ht

/-- Every original full row is the same quiet physical profile plus all
of its nonquiet coefficients. No error price is assigned to the background. -/
theorem RelativeBudget.native_background_split
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (hblock : p.B = P.p.B) {δ ε : ℝ}
    (hV : P.activities.Valid P.p δ ε) (x : X) (box : Box n) (U : Config G n) :
    OverlayForcedBarcode.full (T.leaf x).contents box U =
      Poly.send R.quiet
        (profile P.activities (fun i => Complex.ofReal ∘ P.activities.K i) box U) +
      Poly.inject (fun q => if q = R.quiet then 0 else
        (OverlayForcedBarcode.full (T.leaf x).contents box U).part q) := by
  apply Marker.Poly.ext
  intro q
  rw [Poly.part_plus, Poly.part_send]
  change (OverlayForcedBarcode.full (T.leaf x).contents box U).part q =
    (if q = R.quiet then
      profile P.activities (fun i => Complex.ofReal ∘ P.activities.K i) box U else 0) +
    (if q = R.quiet then 0 else
      (OverlayForcedBarcode.full (T.leaf x).contents box U).part q)
  by_cases hq : q = R.quiet
  · subst q
    rw [if_pos rfl, if_pos rfl, add_zero]
    exact h.native_full_quiet hc hblock hV x box U
  · rw [if_neg hq, if_neg hq, zero_add]

end YM.Integration.LocalComparison
