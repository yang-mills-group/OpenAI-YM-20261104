import YM.Integration.RiderTasteRegular
import YM.Integration.LocalComparisonFunctionalRetains
import YM.FVA1.LeafRoster
import YM.Extra.SOURCE_HISTORIES.Unit

/-! A fixed finite native Page family as a full Taste.  The original forced
Nat indices, support metadata, vacuum K and admissibility predicate are retained.
Only the scalar Page coefficients vary with the independent tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QlocalFinitePageTaste
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay FVA1
open Extra.Trajectories RG3.Press RG3.Held RG3.Forms RG3.Script.Picnic
open RiderTastePresentation LocalComparison
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V I Ω : Type} [DecidableEq V]
  [Fintype V] [Nonempty V] [Fintype I] {R : Census V} {P : Rep G n}
  (q : I → Page R P) (o : Positions V n) (f : I → Ω → ℂ)

def raw (x : Ω) (i : I) (U : Config G n) : Poly R :=
  (q i).shellx.elim
    (fun _ => Poly.send (q i).s (f i x * ((q i).term U * (q i).chip)))
    (fun _ => 0)

def ledger : Ledger Ω I G n R where
  region i := Seal.scope P (q i).shellx
  raw := raw q f
  total _ := False
  forced x i U := Poly.bead R (P.activities.K i U : ℂ) +
    ∑ j, (q j).payment (f j x) U i

def presentation : Taste Ω o.origin P R :=
  (ledger q f).taste P o.origin o.stub

omit [Fintype V] [Nonempty V] in
private theorem mode_nonempty (s : R.Mode) (hs : s ≠ R.quiet) :
    s.val.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro h
  apply hs
  exact Subtype.ext h

omit [Fintype V] [Nonempty V] [Fintype I] in
private theorem page_ne_quiet (i : I) : (q i).s ≠ R.quiet := by
  intro h
  exact (q i).marked.ne_empty (congrArg Subtype.val h)

omit [Fintype V] [Nonempty V] in
private theorem raw_supported
    (h : ∀ i v, v ∈ (q i).s.val → o.stub v ⊆ Seal.scope P (q i).shellx)
    (x : Ω) (i : I) (U : Config G n) (s : R.Mode)
    (hn : (raw q f x i U).part s ≠ 0) :
    ∀ v ∈ s.val, o.stub v ⊆ (ledger q f).region i := by
  cases he : (q i).shellx with
  | inr k => simp [raw, he] at hn
  | inl S =>
    have hs : s = (q i).s := by
      by_contra hs
      exact hn (by simp [raw, he, Poly.part_send, hs])
    subst s
    exact h i

omit [Fintype V] [Nonempty V] [Fintype I] in
private theorem payment_supported
    (h : ∀ i v, v ∈ (q i).s.val → o.stub v ⊆ Seal.scope P (q i).shellx)
    (x : Ω) (i : I) (U : Config G n) (k : ℕ) (s : R.Mode)
    (hn : ((q i).payment (f i x) U k).part s ≠ 0) :
    ∀ v ∈ s.val, o.stub v ⊆ (P.activities.forced k).support := by
  cases he : (q i).shellx with
  | inl S => simp [Page.payment, he] at hn
  | inr j =>
    have hj : j = k := by
      by_contra hj
      exact hn (by simp [Page.payment, he, hj])
    subst j
    have hs : s = (q i).s := by
      by_contra hs
      exact hn (by simp [Page.payment, Page.point, he, Poly.part_send, hs])
    subst s
    simpa [Seal.scope, he] using h i

omit [Fintype V] [Nonempty V] in
private theorem painted_eq (x : Ω) (U : Config G n) (i : I) :
    (ledger q f).painted P x U i = (q i).aroma (f i x) U := by
  cases he : (q i).shellx with
  | inl S =>
    by_cases hU : Healthy P.p.threshold S U <;>
      simp [Ledger.painted, ledger, raw, Seal.scope, Page.aroma, Page.point,
        Page.ready, he, masked, hU]
  | inr k =>
    simp [Ledger.painted, ledger, raw, Page.aroma, he, masked]

omit [Fintype V] [Nonempty V] [Fintype I] in
private theorem payment_quiet (x : Ω) (U : Config G n) (i : I) (k : ℕ) :
    ((q i).payment (f i x) U k).part R.quiet = 0 := by
  have h := page_ne_quiet q i
  cases he : (q i).shellx with
  | inl S => simp only [Page.payment, he, Sum.elim_inl, Poly.part_nil]
  | inr j =>
    simp only [Page.payment, he, Sum.elim_inr]
    split_ifs
    · simp only [Page.point, Poly.part_send, if_neg (Ne.symm h)]
    · rfl

omit [Fintype V] [Nonempty V] in
private theorem forced_quiet (x : Ω) (U : Config G n) (k : ℕ) :
    ((ledger q f).forced x k U).part R.quiet = (P.activities.K k U : ℂ) := by
  simp [ledger, Poly.part_plus, Poly.part_sum, payment_quiet, Poly.bead,
    Poly.part_send]

/-- The complete native Page expression, including every original K occurrence. -/
theorem density
    (h : ∀ i v, v ∈ (q i).s.val → o.stub v ⊆ Seal.scope P (q i).shellx)
    (x : Ω) (U : Config G n) :
    ((presentation q o f).leaf x).density U =
      essence q (fun _ => 0) (fun i => f i x) U := by
  have hl : ((presentation q o f).leaf x).log U =
      ∑ i, (q i).aroma (f i x) U := by
    change (((ledger q f).taste P o.origin o.stub).leaf x).log U = _
    rw [(ledger q f).log_sum P o.origin o.stub x U (Summable.of_finite)
      (fun _ h => False.elim h) ?_ ?_, tsum_fintype]
    · exact Finset.sum_congr rfl (fun i _ => painted_eq q f x U i)
    · intro k hk
      by_contra hn
      apply hk
      change ∀ v ∈ k.2.val.val, o.stub v ⊆ (ledger q f).region k.1
      have hr : (raw q f x k.1 U).part k.2.val ≠ 0 := by
        intro hz
        apply hn
        simp only [Ledger.painted, ledger, if_false, masked,
          Set.indicator_apply, Set.mem_setOf_eq]
        split_ifs <;> simp_all
      exact raw_supported q o f h x k.1 U k.2.val hr
    · intro i
      rw [painted_eq]
      have hi := page_ne_quiet q i
      cases he : (q i).shellx <;>
        simp [Page.aroma, Page.point, he, Poly.part_send, Ne.symm hi]
  have hc := (ledger q f).forced_cluster P o.origin o.stub x U
    (fun i => forced_quiet q f x U i)
  change (Real.exp (P.exponent U) : ℂ) •
    (Poly.pass (((presentation q o f).leaf x).log U) *
      (((ledger q f).taste P o.origin o.stub).menu.terms x).cluster U) = _
  rw [hl, hc]
  simp only [essence, MergeProof.Accent.Mach, Poly.send_zero,
    Finset.sum_const_zero, zero_add, ledger]

/-- A nonzero forced coefficient retains the original full Page stubs. -/
theorem functionalRetains
    (h : ∀ i v, v ∈ (q i).s.val → o.stub v ⊆ Seal.scope P (q i).shellx) :
    FunctionalRetains (presentation q o f) o.stub := by
  let _ := (inferInstance : Fintype V)
  refine ⟨o.mem, ?_, ?_, ?_⟩
  · intro i v _ hv
    exact (ledger q f).regular_covers P o.origin o.stub i v hv
  · intro i j v hn hv
    rcases hn with ⟨x, U, hn⟩
    by_cases hj : j ∈ Set.range (pin : Key ℕ R → ℕ)
    · obtain ⟨k, rfl⟩ := hj
      have hki : k.1 = i := by
        by_contra hi
        exact hn (by simp [presentation, Ledger.taste, Ledger.view, hi])
      have hpart : ((ledger q f).forced x i U).part k.2.val ≠ 0 := by
        simpa [presentation, Ledger.taste, Ledger.view, hki] using hn
      have hmem : v ∈ k.2.val.val := by
        simpa [presentation, Ledger.taste, Ledger.view, codedMode] using hv
      have hsum : (∑ a, ((q a).payment (f a x) U i).part k.2.val) ≠ 0 := by
        simpa [ledger, Poly.part_plus, Poly.part_sum, Poly.bead,
          Poly.part_send, k.2.property] using hpart
      by_contra hmissing
      apply hsum
      apply Finset.sum_eq_zero
      intro a _
      by_contra ha
      exact hmissing (payment_supported q o f h x a U i k.2.val ha v hmem)
    · exact False.elim (hn (by
        simp [presentation, Ledger.taste, Ledger.view, unpin_blank _ _ hj]))
  · intro i v _ hv
    exact (ledger q f).caption_covers P o.origin o.stub i v hv

omit [Fintype V] in
private theorem regular_zero (x : Ω) (hx : ∀ i, f i x = 0) (i : ℕ) :
    (presentation q o f).menu.regular x i = 0 := by
  funext U
  by_cases hi : i ∈ Set.range
      (pin : (ledger q f).RegularKey o.stub → ℕ)
  · obtain ⟨k, rfl⟩ := hi
    simp [presentation, Ledger.taste, Ledger.view, ledger, raw, hx]
  · simp [presentation, Ledger.taste, Ledger.view, unpin_blank _ _ hi]

omit [Fintype V] in
private theorem force_zero (x : Ω) (hx : ∀ i, f i x = 0) (i j : ℕ) :
    (presentation q o f).menu.force x i j = 0 := by
  by_cases hj : j ∈ Set.range (pin : Key ℕ R → ℕ)
  · obtain ⟨k, rfl⟩ := hj
    funext U
    have hz (a : I) : (q a).payment (f a x) U k.1 = 0 := by
      cases he : (q a).shellx <;> simp [Page.payment, Page.point, he, hx]
    simp [presentation, Ledger.taste, Ledger.view, ledger, hz, Poly.bead,
      Poly.part_send, k.2.property]
  · simp [presentation, Ledger.taste, Ledger.view, unpin_blank _ _ hj]

/-- The zero test has the same declared rows and the original vacuum gas. -/
theorem active_zero (x : Ω) (hx : ∀ i, f i x = 0) :
    ((presentation q o f).leaf x).Active := by
  let _ := (inferInstance : Fintype V)
  have hp (i : ℕ) : ((presentation q o f).menu.rays i).val.Nonempty := by
    by_cases hi : i ∈ Set.range
        (pin : (ledger q f).RegularKey o.stub → ℕ)
    · obtain ⟨k, rfl⟩ := hi
      simpa [presentation] using mode_nonempty k.val.2.val k.val.2.property
    · simp [presentation, Ledger.taste, Ledger.view, unpin_blank _ _ hi,
        Census.fire]
  have ho (i j : ℕ) : ((presentation q o f).menu.marks i j).val.Nonempty := by
    by_cases hj : j ∈ Set.range (pin : Key ℕ R → ℕ)
    · obtain ⟨k, rfl⟩ := hj
      simpa [presentation, Ledger.taste, Ledger.view, codedMode] using
        mode_nonempty k.2.val k.2.property
    · simp [presentation, Ledger.taste, Ledger.view, codedMode,
        unpin_blank _ _ hj, Census.fire]
  refine ⟨⟨hp, ?_, ?_, ho, ?_, ?_, ?_, ?_, ?_⟩, ⟨hp, ?_⟩⟩
  · intro i v hv
    exact (ledger q f).regular_covers P o.origin o.stub i v hv (o.mem v)
  · intro i
    change P.p.Regular _ ((presentation q o f).menu.regular x i)
    rw [regular_zero q o f x hx]
    exact (Extra.Histories.regular0 P.p _ (0 : Site n)).1
  · intro i j hn
    exact False.elim (hn (force_zero q o f x hx i j))
  · intro i j
    change UsesFinal _ _ ((presentation q o f).menu.force x i j)
    rw [force_zero q o f x hx]
    intro U W hU hW
    rfl
  · intro i j U hn
    exact False.elim (hn (congrFun (force_zero q o f x hx i j) U))
  · intro i j
    change Measurable ((presentation q o f).menu.force x i j)
    rw [force_zero q o f x hx]
    exact measurable_const
  · intro i j
    change GaugeInvariant ((presentation q o f).menu.force x i j)
    rw [force_zero q o f x hx]
    intro a U
    rfl
  · intro i v hv
    exact (ledger q f).caption_covers P o.origin o.stub i v hv (o.mem v)

section Multilinear
variable (D : V → ComparisonDensity.Address.Orbit)
  (g : I → TestSpace D → ℂ)
  (hg : ∀ i, Letter ℂ (fun v => (D v).Mood) (q i).s.val (g i))

omit [Fintype V] [Nonempty V] in
private theorem send_published (s : R.Mode) (a : TestSpace D → ℂ)
    (ha : Letter ℂ (fun v => (D v).Mood) s.val a) :
    Published (K := ℂ) (fun v => (D v).Mood) (fun x => Poly.send s (a x)) := by
  intro j
  simp only [Poly.part_send]
  by_cases hj : j = s
  · subst j
    simpa only [ite_true] using ha
  · simp only [if_neg hj]
    exact Letter.still

include hg

omit [Fintype V] [Nonempty V] [Fintype I] in
private theorem point_published (i : I) (U : Config G n) :
    Published (K := ℂ) (fun v => (D v).Mood)
      (fun x => (q i).point (g i x) U) := by
  change Published (K := ℂ) (fun v => (D v).Mood)
    (fun x => Poly.send (q i).s (g i x * ((q i).ready U * (q i).chip)))
  apply send_published D
  simpa only [mul_comm] using
    (hg i).cmul ((q i).ready U * (q i).chip)

omit [Fintype V] [Nonempty V] [Fintype I] in
private theorem raw_published (i : I) (U : Config G n) :
    Published (K := ℂ) (fun v => (D v).Mood)
      (fun x => raw q g x i U) := by
  cases he : (q i).shellx with
  | inl S =>
    simp only [raw, he, Sum.elim_inl]
    apply send_published D
    simpa only [mul_comm] using (hg i).cmul ((q i).term U * (q i).chip)
  | inr k =>
    simp only [raw, he, Sum.elim_inr]
    exact Published.zero

omit [Fintype V] [Nonempty V] [Fintype I] in
private theorem payment_published (i : I) (U : Config G n) (k : ℕ) :
    Published (K := ℂ) (fun v => (D v).Mood)
      (fun x => (q i).payment (g i x) U k) := by
  cases he : (q i).shellx with
  | inl S =>
    simp only [Page.payment, he, Sum.elim_inl]
    exact Published.zero
  | inr j =>
    simp only [Page.payment, he, Sum.elim_inr]
    by_cases hj : j = k
    · simp only [if_pos hj]
      exact point_published q D g hg i U
    · simp only [if_neg hj]
      exact Published.zero

omit [Fintype V] [Nonempty V] in
private theorem forced_published (U : Config G n) (k : ℕ) :
    Published (K := ℂ) (fun v => (D v).Mood)
      (fun x => (ledger q g).forced x k U) := by
  have h0 : Published (K := ℂ) (fun v => (D v).Mood)
      (fun _ : TestSpace D => Poly.bead R (P.activities.K k U : ℂ)) := by
    apply Published.const
    intro i hi
    simp [Poly.bead, Poly.part_send, hi]
  have h1 : Published (K := ℂ) (fun v => (D v).Mood)
      (fun x => ∑ i, (q i).payment (g i x) U k) := by
    simpa only [tsum_fintype] using
      (Published.assembly (fun i x => (q i).payment (g i x) U k)
        (fun i => payment_published q D g hg i U k)
        (fun _ => Summable.of_finite))
  exact h0.sum h1

/-- Each fixed row uses exactly its original marked independent test slots. -/
theorem multilinear : Multilinear D (presentation q o g) := by
  let _ := (inferInstance : Fintype V)
  constructor
  · intro i U
    by_cases hi : i ∈ Set.range
        (pin : (ledger q g).RegularKey o.stub → ℕ)
    · obtain ⟨k, rfl⟩ := hi
      simpa [presentation, Ledger.taste, Ledger.view, ledger] using
        raw_published q D g hg k.val.1 U k.val.2.val
    · simp only [presentation, Ledger.taste, Ledger.view, unpin_blank _ _ hi,
        Pi.zero_apply]
      exact Letter.still
  · intro i j U
    by_cases hj : j ∈ Set.range (pin : Key ℕ R → ℕ)
    · obtain ⟨k, rfl⟩ := hj
      by_cases hki : k.1 = i
      · simpa [presentation, Ledger.taste, Ledger.view, codedMode, hki] using
          forced_published q D g hg U k.1 k.2.val
      · simp only [presentation, Ledger.taste, Ledger.view, codedMode,
          unpin_pin, if_neg hki]
        exact Letter.still
    · simp only [presentation, Ledger.taste, Ledger.view, codedMode,
        unpin_blank _ _ hj, Pi.zero_apply]
      exact Letter.still
  · intro v
    exact Letter.still
  · intro i
    have hz (x : TestSpace D) : (presentation q o g).score x i = 0 := by
      by_cases hi : i ∈ Set.range
          (pin : (ledger q g).RegularKey o.stub → ℕ)
      · obtain ⟨k, rfl⟩ := hi
        simp [presentation, Ledger.taste, ledger]
      · simp [presentation, Ledger.taste, unpin_blank _ _ hi]
    constructor
    · intro x y _
      exact (hz x).trans (hz y).symm
    · intro x j hj a b
      rw [hz, hz, hz, add_zero]
    · intro x j hj a b
      rw [hz, hz, smul_zero]
end Multilinear

end YM.Integration.QlocalFinitePageTaste
