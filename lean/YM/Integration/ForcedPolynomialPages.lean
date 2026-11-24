import YM.FVA1.LeafRoster
import YM.Integration.NativeForcedPolynomialReentry

/-!
Finite full-polynomial partners on the original forced dictionary.  The index
retains all nonempty modes whose whole original stubs fit the complete support.
Original flag inventories and extra tests are supplied by the literal Keeper.
This algebraic constructor does not assert a small rooted price.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ForcedPolynomialPages
open Finset Function MeasureTheory Lattice Wilson RG Marker FVA1
open MergeProof MergeProof.Accent Planned.GuardedAtom Extra.Histories
open Push.GridApprox.Nil
open OriginalForcedAddresses
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
    {Γ : Census V} {P : Rep G n}

/-- This metadata is fixed before the coefficient function or its tests. -/
abbrev Modes (o : Positions V n) (s : StockTag n) :=
  {q : Γ.Mode // q.val.Nonempty ∧ ∀ i ∈ q.val, o.stub i ⊆ s.val.1}

abbrev Index (o : Positions V n) := Σ s : StockTag n, Modes (Γ := Γ) o s

def page (K : Guard.Keeper P.p P.activities) (o : Positions V n)
    (F : Box n → Config G n → Poly Γ) (j : Index (Γ := Γ) o) : Page Γ P where
  s := j.2.val
  marked := j.2.property.1
  shellx := .inr (cart K j.1)
  term U := (F j.1.val U).part j.2.val
  chip := 1

/-- Neither the full support nor the original partner predicate is discarded. -/
theorem entry (K : Guard.Keeper P.p P.activities) (o : Positions V n)
    (F : Box n → Config G n → Poly Γ)
    (hF : ∀ s, Flow o.origin s (F s) P.p.threshold)
    (j : Index (Γ := Γ) o) (b : ℝ)
    (hb : ∀ U, ‖(F j.1.val U).part j.2.val‖ ≤ b) :
    (page K o F j).Entry o b := by
  have hs : (P.activities.forced (cart K j.1)).support = j.1.val.1 :=
    congrArg Prod.fst (cardK K j.1)
  have hi : (P.activities.forced (cart K j.1)).inventory = j.1.val.2 :=
    congrArg Prod.snd (cardK K j.1)
  refine ⟨?_, ?_, ?_⟩
  · intro i hmem
    change o.stub i ⊆ (P.activities.forced (cart K j.1)).support
    rw [hs]
    exact j.2.property.2 i hmem
  · intro s he
    cases he
  intro k he
  change Sum.inr (cart K j.1) = Sum.inr k at he
  have hk := Sum.inr.inj he
  subst k
  refine ⟨fun g U => congrArg (fun z => z.part j.2.val)
    ((hF j.1.val).turns g U), (hF j.1.val).me _, ?_, ?_⟩
  · rw [hs]
    intro U W hsites hflags
    exact congrArg (fun z => z.part j.2.val)
      ((hF j.1.val).home U W hsites hflags)
  intro U
  refine ⟨hb U, ?_⟩
  intro hn
  have hpoly : F j.1.val U ≠ 0 := fun hz => hn (by
    change (F j.1.val U).part j.2.val = 0
    rw [hz]
    rfl)
  have hf : (P.activities.forced (cart K j.1)).support ∩ flags P.p.threshold U =
      (P.activities.forced (cart K j.1)).inventory := by
    rw [hs, hi]
    exact ((hF j.1.val).permits U hpoly).1
  exact ⟨hf, K.pass (j.1, 0) U hf⟩

theorem due_exact (K : Guard.Keeper P.p P.activities) (o : Positions V n)
    (F : Box n → Config G n → Poly Γ) (j : Index (Γ := Γ) o)
    (w : V → ℝ) (b : ℝ) :
    (page K o F j).due w b = Poly.toll w j.2.val * b := by
  simp only [Page.due, page, norm_one, mul_one]

variable [Fintype V]

/-- Every omitted mode is genuinely zero: either quiet, or violating a whole
stub inclusion proved for the original coefficient function. -/
theorem sum_modes (o : Positions V n) (F : Box n → Config G n → Poly Γ)
    (hq : ∀ s U, (F s U).part Γ.quiet = 0)
    (hs : ∀ s U q, (F s U).part q ≠ 0 →
      ∀ i ∈ q.val, o.stub i ⊆ s.1)
    (s : StockTag n) (U : Config G n) :
    (∑ q : Modes (Γ := Γ) o s, Poly.send q.val ((F s.val U).part q.val)) =
      F s.val U := by
  apply funext
  intro q
  change (Poly.get q) (∑ a : Modes (Γ := Γ) o s,
    Poly.send a.val ((F s.val U).part a.val)) = (F s.val U).part q
  rw [map_sum]
  change (∑ a : Modes (Γ := Γ) o s,
    (Poly.send a.val ((F s.val U).part a.val)).part q) = (F s.val U).part q
  by_cases hq' : q.val.Nonempty ∧ ∀ i ∈ q.val, o.stub i ⊆ s.val.1
  · rw [Finset.sum_eq_single (⟨q, hq'⟩ : Modes (Γ := Γ) o s)]
    · exact (Poly.part_send ..).trans (if_pos rfl)
    · intro a _ ha
      have he : q ≠ a.val := by
        intro he
        exact ha (Subtype.ext he.symm)
      exact (Poly.part_send ..).trans (if_neg he)
    · simp
  have hz : (F s.val U).part q = 0 := by
    by_contra hn
    apply hq'
    refine ⟨?_, hs s.val U q hn⟩
    by_contra he
    have hquiet : q = Γ.quiet :=
      Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp he)
    exact hn (by simpa only [hquiet] using hq s.val U)
  rw [hz]
  apply Finset.sum_eq_zero
  intro a _
  rw [Poly.part_send]
  split
  · rename_i he
    exact (hq' (he.symm ▸ a.property)).elim
  rfl

/-- All mixed-mode payments add to the full correction at its original Nat
address; this is not only a singleton or quiet-coefficient identity. -/
theorem sum_payment (K : Guard.Keeper P.p P.activities) (o : Positions V n)
    (F : Box n → Config G n → Poly Γ)
    (hq : ∀ s U, (F s U).part Γ.quiet = 0)
    (hs : ∀ s U q, (F s U).part q ≠ 0 →
      ∀ i ∈ q.val, o.stub i ⊆ s.1)
    (U : Config G n) (k : ℕ) :
    (∑ j : Index (Γ := Γ) o, (page K o F j).payment 1 U k) =
      NativeForcedPolynomialReentry.rebook K F k U := by
  rw [Fintype.sum_sigma]
  simp only [page, Page.payment, Page.point, Page.ready, Sum.elim_inr,
    mul_one, one_mul]
  by_cases hk : k ∈ Set.range (cart K)
  · obtain ⟨s, rfl⟩ := hk
    rw [NativeForcedPolynomialReentry.at_address]
    rw [Finset.sum_eq_single s]
    · simpa only [ite_true] using sum_modes o F hq hs s U
    · intro a _ ha
      have he : cart K a ≠ cart K s := fun h => ha ((cart K).injective h)
      simp only [if_neg he, Finset.sum_const_zero]
    · simp
  rw [NativeForcedPolynomialReentry.off_address K F hk]
  change _ = 0
  apply Finset.sum_eq_zero
  intro s _
  have he : cart K s ≠ k := fun h => hk ⟨s, h⟩
  simp only [if_neg he, Finset.sum_const_zero]

/-- Filtering the genuine nonzero partner modes loses no mode-count factor.
The common sheet price is paid once at this original complete support. -/
theorem sum_due_le (K : Guard.Keeper P.p P.activities) (o : Positions V n)
    (F : Box n → Config G n → Poly Γ) (s : StockTag n)
    (w : V → ℝ) (hw : ∀ i, 0 < w i) (b : Sheet Γ) (hb : 0 ≤ b) :
    (∑ q : Modes (Γ := Γ) o s, (page K o F ⟨s, q⟩).due w (b q.val)) ≤
      wordsPrice w b := by
  simp only [due_exact]
  have he :
      (∑ q ∈ (Finset.univ : Finset (Modes (Γ := Γ) o s)).image Subtype.val,
        Poly.toll w q * b q) =
      ∑ q : Modes (Γ := Γ) o s, Poly.toll w q.val * b q.val := by
    exact Finset.sum_image fun _ _ _ _ h => Subtype.ext h
  rw [← he]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro q _ _
  exact mul_nonneg (Poly.worth hw q).le (hb q)

end YM.Integration.ForcedPolynomialPages
