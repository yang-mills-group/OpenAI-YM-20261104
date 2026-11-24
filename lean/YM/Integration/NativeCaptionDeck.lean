import YM.PE.Arc.Papyrus

/-!
Exact native Deck regrouping of finite original-support rows, including
unmasked constant captions.  The regular input is merely Borne and quiet;
it is not required to be Healthy-masked.  Each entire coefficient is split
on the Healthy predicate of its enlarged true-root cover.  The complementary
piece is retained as an ash atom and participates in the same forced gas.

The countable native Rider rows are aggregated before this construction;
no truncation, change of vacuum, or assumed grouped Served is used here.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativeCaptionDeck
open Finset Function MeasureTheory Marker Extra.Trajectories
open MergeProof MergeProof.Accent MergeProof.Replicum MergeProof.Replicums
open Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical

variable {arity : ℕ} {V A : Type*} [DecidableEq V] [Fintype V]
    {G : Gauge} {n : Side}

structure Input (arity : ℕ) (V A : Type*) [DecidableEq V] [Fintype V]
    (G : Gauge) (n : Side) where
  roots : Name arity V → Site n
  region : A → Support n
  regular : A → Config G n → Poly (Aged arity V)
  forced : Box n → Config G n → Poly (Aged arity V)

namespace Input
variable (Z : Input arity V A G n) (t : ℝ)

/-- The native input properties are weaker than Carton: constant captions
may have any nonzero degree and need not vanish off the Healthy chart. -/
structure Admitted (t : ℝ) : Prop where
  regular a : Borne Z.roots (Z.region a) (Z.regular a) t
  quiet a U : (Z.regular a U).part (Aged arity V).quiet = 0
  forced p : Flow Z.roots p (Z.forced p) t

abbrev RegularKey :=
  {i : A × (Aged arity V).Mode //
    i.2.val.Nonempty ∧ i.2.val.image Z.roots ⊆ Z.region i.1}

abbrev ForcedKey :=
  {i : Box n × (Aged arity V).Mode //
    Sure i.1 ∧ i.2.val.image Z.roots ⊆ i.1.1}

abbrev Seed := Z.RegularKey × Bool

def focus (v : V) : Site n := Z.roots (v, 0)

/-- Every old support is retained; only the actual grouped roots are added. -/
def cover (s : Support n) (q : (Aged arity V).Mode) : Support n :=
  s ∪ (span q).val.image Z.focus

def piece (U : Config G n) (i : Z.Seed) : ℂ :=
  if Healthy t (Z.cover (Z.region i.1.val.1) i.1.val.2) U ↔ i.2 = true
  then (Z.regular i.1.val.1 U).part i.1.val.2 else 0

def deck : Deck arity V Z.Seed Z.ForcedKey G n where
  mode_ := Sum.elim (fun i => i.1.val.2) (fun i => i.val.2)
  wick i := Z.region i.1.val.1
  spill i := i.val.1
  cover := Sum.elim
    (fun i => Z.cover (Z.region i.1.val.1) i.1.val.2)
    (fun i => Z.cover i.val.1.1 i.val.2)
  toll := Sum.elim (fun i U => Z.piece t U i)
    (fun i U => (Z.forced i.val.1 U).part i.val.2)
  ash i := i.2 = false
  seat := Z.focus

variable (h : Z.Admitted t)
include h

theorem wet : (Z.deck t).Wet t := by
  refine ⟨fun i => ?_, fun i v => ?_, fun i => i.1.property.1,
    fun i => i.property.1, fun i U he hx hy => hx ?_,
    fun i U hp => (h.forced i.val.1 |>.permits U ?_).1,
    fun i hi => ?_⟩
  · cases i <;> exact subset_union_left
  · intro hv
    cases i <;> exact subset_union_right (mem_image_of_mem _ hv)
  · exact if_neg (fun hz => Bool.false_ne_true
      ((show i.2 = false from he).symm.trans (hz.1 hy)))
  · exact fun he => hp (by
      change (Z.forced i.val.1 U).part _ = _
      rw [he, Poly.part_nil])
  change (span i.val.2).val = ∅ at hi
  unfold deck
  simp [cover, Sum.elim, hi]

theorem coefficient_properties (i : Z.RegularKey) :
    UsesFinal t (Z.region i.val.1)
      (fun U => (Z.regular i.val.1 U).part i.val.2) ∧
    Measurable (fun U => (Z.regular i.val.1 U).part i.val.2) ∧
    GaugeInvariant (fun U => (Z.regular i.val.1 U).part i.val.2) := by
  refine ⟨fun X Y hx hy => congrArg
    (fun p : Poly (Aged arity V) => p.part i.val.2)
    ((h.regular i.val.1).home X Y hx hy), (h.regular _).me i.val.2,
    fun s U => ?_⟩
  exact congrArg (fun p : Poly (Aged arity V) => p.part i.val.2)
    ((h.regular _).turns s U)

theorem piece_properties (i : Z.Seed) :
    UsesFinal t (Z.cover (Z.region i.1.val.1) i.1.val.2)
      (fun U => Z.piece t U i) ∧
    Measurable (fun U => Z.piece t U i) ∧
    GaugeInvariant (fun U => Z.piece t U i) := by
  let K := Z.cover (Z.region i.1.val.1) i.1.val.2
  obtain ⟨hx, hp, hz⟩ := Z.coefficient_properties t h i.1
  have hr : UsesFinal t K
      (fun U => (Z.regular i.1.val.1 U).part i.1.val.2) :=
    Work.H03.reads_larger subset_union_left hx
  refine ⟨fun X Y ha hb => ?_, Measurable.ite ?_ hp measurable_const,
    fun s U => ?_⟩
  · change (if Healthy t K X ↔ _ then _ else _) =
      (if Healthy t K Y ↔ _ then _ else _)
    unfold Healthy
    have hr' : (Z.regular i.1.val.1 X).part i.1.val.2 =
        (Z.regular i.1.val.1 Y).part i.1.val.2 := hr X Y ha hb
    rw [disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty, hb, hr']
  · by_cases hh : i.2 = true
    · simp only [hh, iff_true, Healthy, disjoint_iff_inter_eq_empty]
      exact census_me t K ∅
    simp only [hh, Bool.false_eq_true, iff_false, Healthy,
      disjoint_iff_inter_eq_empty]
    exact (census_me t K ∅).compl
  unfold piece Healthy
  simp only [gauge_flags, hz s U]
  congr

theorem smooth : (Z.deck t).Smooth t := by
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun i U hi hV => ?_⟩
  · cases j with
    | inl i => exact (Z.piece_properties t h i).1
    | inr i =>
      apply Work.H03.reads_larger (p := i.val.1.1) subset_union_left
        (fun X Y hp hv => ?_)
      exact congrArg (fun p : Poly (Aged arity V) => p.part i.val.2)
        ((h.forced _).home X Y hp hv)
  · cases j with
    | inl i => exact (Z.piece_properties t h i).2.1
    | inr i => exact (h.forced _).me i.val.2
  · cases j with
    | inl i => exact (Z.piece_properties t h i).2.2
    | inr i =>
      exact fun s U => congrArg
        (fun p : Poly (Aged arity V) => p.part i.val.2)
        ((h.forced _).turns s U)
  change ¬ i.2 = false at hi
  change Z.piece t U i ≠ 0 at hV
  unfold piece at hV
  split at hV
  · rename_i he
    exact he.2 (by simpa using hi)
  contradiction

variable [Fintype A]

omit [Fintype A] in
/-- Barcode aggregation reconstructs the complete original forced row. -/
theorem forced_sum (U : Config G n) (i : Box n) :
    cram (Z.deck t).spill
      (fun j => Poly.send ((Z.deck t).mode_ (.inr j))
        ((Z.deck t).toll (.inr j) U)) i = Z.forced i U := by
  apply Marker.Poly.ext
  intro p
  unfold cram
  rw [Poly.share Summable.of_finite, tsum_fintype]
  let K := {a : Z.ForcedKey // (Z.deck t).spill a = i}
  change ∑ a : K, (Poly.send a.val.val.2
    ((Z.forced a.val.val.1 U).part a.val.val.2)).part p =
      (Z.forced i U).part p
  by_cases hh : (Z.forced i U).part p = 0
  · rw [hh]
    refine sum_eq_zero fun a _ => ?_
    rw [Poly.part_send]
    split
    · rename_i he
      rw [show a.val.val.1 = i from a.property, ← he, hh]
    rfl
  have ht := (h.forced i).permits U
    (fun he => hh (by rw [he, Poly.part_nil]))
  let v : Z.ForcedKey := ⟨(i, p), ht.2, (h.forced i).toBorne.place _ _ hh⟩
  let b : K := ⟨v, rfl⟩
  rw [sum_eq_single b]
  · exact (Poly.part_send ..).trans (if_pos rfl)
  · intro x _ hx
    rw [Poly.part_send]
    exact if_neg (fun he => hx
      (Subtype.ext (Subtype.ext (Prod.ext x.property he.symm))))
  simp

/-- Both halves of every caption are included before grouping. -/
theorem regular_sum (U : Config G n) :
    ∑ j : Z.Seed, Poly.send ((Z.deck t).mode_ (.inl j))
      ((Z.deck t).toll (.inl j) U) = ∑ i, Z.regular i U := by
  let f b i := Poly.send b.val.2 (Z.piece t U (b, i))
  have hh (b : Z.RegularKey) :
      ∑ i : Bool, f b i =
        Poly.send b.val.2 ((Z.regular b.val.1 U).part b.val.2) := by
    unfold f
    rw [Fintype.sum_bool]
    unfold piece
    by_cases he : Healthy t (Z.cover (Z.region b.val.1) b.val.2) U <;>
      simp [he]
  change ∑ i : Z.RegularKey × Bool, f i.1 i.2 = _
  rw [Fintype.sum_prod_type]
  simp_rw [hh]
  let g (i : Z.RegularKey) :=
    Poly.send i.val.2 ((Z.regular i.val.1 U).part i.val.2)
  have he := (border (fun i : Z.RegularKey => i.val.1)
    (p := g) Summable.of_finite).tsum_eq
  rw [tsum_fintype, tsum_fintype] at he
  change ∑ j : Z.RegularKey, g j = _
  rw [← show ∑ l : A, ∑' i : {i : Z.RegularKey // i.val.1 = l}, g i.val =
    ∑ i : Z.RegularKey, g i from he]
  refine sum_congr rfl fun i _ => ?_
  apply Marker.Poly.ext
  intro p
  rw [Poly.share Summable.of_finite, tsum_fintype]
  let K := {j : Z.RegularKey // j.val.1 = i}
  change ∑ a : K, (Poly.send a.val.val.2
    ((Z.regular a.val.val.1 U).part a.val.val.2)).part p =
      (Z.regular i U).part p
  by_cases hh : (Z.regular i U).part p = 0
  · rw [hh]
    refine sum_eq_zero fun a _ => ?_
    rw [Poly.part_send]
    split
    · rename_i he
      rw [a.property, ← he, hh]
    rfl
  have hz : p.val.Nonempty := nonempty_iff_ne_empty.mpr (fun he => hh (by
    rw [show p = (Aged arity V).quiet from Subtype.ext he]
    exact h.quiet i U))
  let a : K := ⟨⟨(i, p), hz, (h.regular i).place _ _ hh⟩, rfl⟩
  rw [sum_eq_single a]
  · exact (Poly.part_send ..).trans (if_pos rfl)
  · intro x _ hx
    rw [Poly.part_send]
    exact if_neg (fun he => hx
      (Subtype.ext (Subtype.ext (Prod.ext x.property he.symm))))
  simp

def regularOutput := (Z.deck t).sky t
def forcedOutput := (Z.deck t).clay t

/-- Actual native regrouping, with no multiplicativity assumption on reap. -/
theorem regroup (U : Config G n) :
    reap (Poly.pass (∑ i, Z.regular i U) *
      field (fun i => Z.forced i U) (flags t U)) =
    Poly.pass (∑ i, Z.regularOutput t i U) *
      field (fun i => Z.forcedOutput t i U) (flags t U) := by
  have he := (Z.deck t).startOld t U (Z.wet t h)
  rw [Z.regular_sum t h U,
    show cram (Z.deck t).spill
      (fun i => Poly.send ((Z.deck t).mode_ (.inr i))
        ((Z.deck t).toll (.inr i) U)) = _ from
      funext (Z.forced_sum t h U)] at he
  exact he

/-- The full original quiet gas survives the off-Healthy redistribution. -/
theorem quiet_preserved (U : Config G n) (i : Box n) :
    (Z.forcedOutput t i U).part (Bud V).quiet =
      (Z.forced i U).part (Aged arity V).quiet :=
  (Z.deck t).sober t U (Z.wet t h) i |>.trans
    (congrArg (fun p : Poly (Aged arity V) => p.part (Aged arity V).quiet)
      (Z.forced_sum t h U i))

theorem regular_output (i : Support n) :
    Burns Z.focus i (Z.regularOutput t i) t :=
  (Z.deck t).clearBurn t (Z.wet t h) (Z.smooth t h) i

theorem forced_output (i : Box n) :
    Flow Z.focus i (Z.forcedOutput t i) t :=
  (Z.deck t).cloudy t (Z.wet t h) (Z.smooth t h) i

end Input
end YM.Integration.NativeCaptionDeck
