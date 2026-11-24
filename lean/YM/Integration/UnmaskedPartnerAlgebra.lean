import YM.Integration.NativeCaptionDeck

/-! Exact dry/forced separation, full-stub transport, and the arity-zero marker
map. No original forced amplitude is assumed zero. Staged, not yet validated. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunUnmaskedPartners
open Finset Function MeasureTheory Lattice Wilson RG Marker
open MergeProof MergeProof.Accent MergeProof.Replicum MergeProof.Replicums
open scoped BigOperators Classical

section DryMerger
variable {arity : ℕ} {V I J : Type*} [DecidableEq V] [Fintype V]
    {G : Gauge} {n : Side}
    (D : Deck arity V I J G n)

/-- This is a property of the native dry index, not a hypothesis that the
original forced amplitude vanishes.  All forced vertices still enter clay. -/
theorem paper_no_forced (i : D.Paper) (j : J) :
    Sum.inr j ∉ i.val := by
  intro hj
  exact i.property.dry ⟨_, hj, trivial⟩

theorem dry_leaf_zero (t : ℝ)
    (hz : ∀ i, ¬ D.ash i → ∀ U, D.toll (.inl i) U = 0)
    (i : D.Paper) (U : Config G n) : D.leaf t (.inl i) U = 0 := by
  obtain ⟨j | j, hj⟩ := i.property.fire.1
  · have hn : ¬ D.ash j := fun he => i.property.dry ⟨_, hj, he⟩
    change Poly.send _ (∏ k ∈ i.val, D.toll k U) = 0
    rw [Finset.prod_eq_zero hj (hz j hn U), Poly.send_zero]
  exact False.elim (paper_no_forced D i j hj)

theorem sky_zero (t : ℝ)
    (hz : ∀ i, ¬ D.ash i → ∀ U, D.toll (.inl i) U = 0) :
    D.sky t = 0 := by
  funext s U
  change (∑' i : {i : D.Paper // D.reach i.val = s},
    D.leaf t (.inl i.val) U) = 0
  simp only [dry_leaf_zero D t hz, tsum_zero]

/-- Full prescribed stubs are transported through the actual native glyph
union.  Origin-only Flow.scope is not substituted for this receipt. -/
theorem leaf_stubs (t : ℝ) (stub : V → Support n)
    (hs : ∀ j U, D.toll j U ≠ 0 → ∀ i ∈ D.roster j, stub i ⊆ D.cover j)
    (j : D.Quills) (U : Config G n) (q : (Bud V).Mode)
    (hq : (D.leaf t j U).part q ≠ 0) (i : V) (hi : i ∈ q.val) :
    stub i ⊆ D.reach (D.glyph j) := by
  have he : q = D.quip j := by
    by_contra hn
    exact hq ((Poly.part_send ..).trans (if_neg hn))
  have hp : D.sap t U j ≠ 0 := by
    intro hz
    apply hq
    change (Poly.send _ (D.sap t U j)).part _ = 0
    rw [hz, Poly.send_zero, Poly.part_nil]
  have hb : D.bud U j ≠ 0 := by
    cases j with
    | inl j => exact hp
    | inr j =>
      intro hz
      apply hp
      change D.nectar t U j = 0
      unfold Deck.nectar
      split
      · exact hz
      rfl
  rw [he, D.paint] at hi
  obtain ⟨a, ha, hi⟩ := Finset.mem_biUnion.mp hi
  have hn : D.toll a U ≠ 0 := fun hz => hb (Finset.prod_eq_zero ha hz)
  exact (hs a U hn i hi).trans (Finset.subset_biUnion_of_mem _ ha)

variable [Fintype I] [Fintype J]

theorem clay_stubs (t : ℝ) (stub : V → Support n)
    (hs : ∀ j U, D.toll j U ≠ 0 → ∀ i ∈ D.roster j, stub i ⊆ D.cover j)
    (s : Box n) (U : Config G n) (q : (Bud V).Mode)
    (hq : (D.clay t s U).part q ≠ 0) (i : V) (hi : i ∈ q.val) :
    stub i ⊆ s.1 := by
  by_contra hn
  apply hq
  change (∑' j : {j : D.Ink // D.fuse j.val = s},
    D.leaf t (.inr j.val) U).part q = 0
  rw [Poly.share (Summable.of_finite)]
  suffices hz : ∀ j : {j : D.Ink // D.fuse j.val = s},
      (D.leaf t (.inr j.val) U).part q = 0 by
    simp only [hz, tsum_zero]
  intro j
  by_contra hj
  have hstub := leaf_stubs D t stub hs (.inr j.val) U q hj i hi
  have hreach : D.reach j.val.val = s.1 := congrArg Prod.fst j.property
  apply hn
  change stub i ⊆ D.reach j.val.val at hstub
  rwa [hreach] at hstub

end DryMerger

section ActualDeckApplication
variable {arity : ℕ} {V A : Type*} [DecidableEq V] [Fintype V]
    {G : Gauge} {n : Side}
    (Z : NativeCaptionDeck.Input arity V A G n) (t : ℝ)

/-- A leak-only input has no healthy regular branch on the enlarged cover. -/
theorem leak_piece_zero
    (hz : ∀ a U, Healthy t (Z.region a) U → Z.regular a U = 0)
    (i : Z.Seed) (hi : ¬ (Z.deck t).ash i) (U : Config G n) :
    (Z.deck t).toll (.inl i) U = 0 := by
  have hb : i.2 = true := by
    change ¬ i.2 = false at hi
    simpa using hi
  change Z.piece t U i = 0
  unfold NativeCaptionDeck.Input.piece
  split
  · rename_i he
    have hcover := he.2 hb
    have hregion : Healthy t (Z.region i.1.val.1) U :=
      hcover.mono_left Finset.subset_union_left
    rw [hz _ U hregion, Poly.part_nil]
  rfl

theorem leak_regular_output_zero
    (hz : ∀ a U, Healthy t (Z.region a) U → Z.regular a U = 0) :
    Z.regularOutput t = 0 :=
  sky_zero (Z.deck t) t (leak_piece_zero Z t hz)

variable [Fintype A]

/-- Full native regrouping of the leak exponential and the complete original
forced input.  No truncation of that forced input or overlap terms occurs. -/
theorem leak_full_regroup (h : Z.Admitted t)
    (hz : ∀ a U, Healthy t (Z.region a) U → Z.regular a U = 0)
    (U : Config G n) :
    reap (Poly.pass (∑ a, Z.regular a U) *
      field (fun s => Z.forced s U) (flags t U)) =
      field (fun s => Z.forcedOutput t s U) (flags t U) := by
  have hr := Z.regroup t h U
  rw [leak_regular_output_zero Z t hz] at hr
  simpa only [Pi.zero_apply, Finset.sum_const_zero,
    Push.GridApprox.Nil.pass_zero, one_mul] using hr

end ActualDeckApplication

section ArityZero
variable {V : Type*} [DecidableEq V] [Fintype V]

/-- At arity zero every original mode contains the whole one-element copy
fiber.  This statement is deliberately not asserted at positive arity. -/
theorem pays_zero (q : (Aged 0 V).Mode) : Pays q := by
  apply (worth_iff q).2
  intro i hi j
  obtain ⟨k, hk⟩ := (spans q i).1 hi
  have he : k = j := Fin.ext (by omega)
  simpa only [he] using hk

theorem zero_reap_tagged_mul (a b : (Aged 0 V).Mode) (x y : ℂ) :
    reap (Poly.send a x * Poly.send b y) =
      Poly.send (span a) x * Poly.send (span b) y := by
  let tags : Fin 2 → (Aged 0 V).Mode := fun i => if i = 0 then a else b
  let values : Fin 2 → ℂ := fun i => if i = 0 then x else y
  have hh := recomp (q := tags) (s := Finset.univ)
    (fun i _ => pays_zero (tags i)) values
  simpa [tags, values, Fin.prod_univ_two] using hh

theorem zero_reap_expansion (x : Poly (Aged 0 V)) :
    reap x = ∑ q, Poly.send (span q) (x.part q) := by
  conv_lhs => rw [← Poly.studs x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Replicum.harvest, if_pos (pays_zero q)]

theorem zero_reap_mul (x y : Poly (Aged 0 V)) :
    reap (x * y) = reap x * reap y := by
  calc
    reap (x * y) = reap ((∑ a, Poly.send a (x.part a)) *
        (∑ b, Poly.send b (y.part b))) := by rw [Poly.studs, Poly.studs]
    _ = ∑ a, ∑ b, reap (Poly.send a (x.part a) *
        Poly.send b (y.part b)) := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum, map_sum]
    _ = ∑ a, ∑ b, Poly.send (span a) (x.part a) *
        Poly.send (span b) (y.part b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact zero_reap_tagged_mul a b _ _
    _ = reap x * reap y := by
      rw [zero_reap_expansion x, zero_reap_expansion y]
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]

def zeroReap : Poly (Aged 0 V) →+* Poly (Bud V) where
  toFun := reap
  map_zero' := map_zero reap
  map_one' := by
    change reap (Poly.send (Aged 0 V).quiet 1) = 1
    rw [Replicum.harvest, if_pos (pays_zero _)]
    rfl
  map_add' := map_add reap
  map_mul' := zero_reap_mul

theorem zero_reap_pass (x : Poly (Aged 0 V)) :
    reap (Poly.pass x) = Poly.pass (reap x) := by
  have hp (k : ℕ) : reap (x ^ k) = reap x ^ k :=
    map_pow zeroReap x k
  have hc : Fintype.card (Name 0 V) = Fintype.card V := by simp [Name]
  unfold Poly.pass
  simp only [map_sum, map_smul, hp, hc]

theorem zero_reap_singletons (f : V → ℂ) :
    reap (∑ i, Poly.send ((Aged 0 V).fire (i, 0)) (f i)) =
      Mach (Bud V) f := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Replicum.harvest, if_pos (pays_zero _)]
  congr 1

theorem zero_reap_bead (c : ℂ) :
    reap (Poly.bead (Aged 0 V) c) = Poly.bead (Bud V) c := by
  change reap (Poly.send (Aged 0 V).quiet c) = _
  rw [Replicum.harvest, if_pos (pays_zero _)]
  rfl

end ArityZero

end YM.Integration.ActualRunUnmaskedPartners
