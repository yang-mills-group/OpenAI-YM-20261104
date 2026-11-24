import YM.Integration.LocalComparisonBlockEnvelope
import YM.RG3.Press.Print
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Exact scalarization of countable polynomial labels for the native `Taste`
representation. The coding retains the original label together with its
nonquiet mode. All rearrangements below use actual summability of the
polynomial family; no representation-norm estimate is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.RiderTastePresentation

open Lattice Wilson RG Marker Overlay Extra.Trajectories
open RG3.Press RG3.Held RG3.Script.Picnic LocalKernelBlocks
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] {R : Census V}

/-- Extract one coefficient and restore it at its original mode. -/
def modeProjection (q : R.Mode) : Poly R →L[ℂ] Poly R where
  toFun f := Poly.send q (f.part q)
  map_add' f g := by
    ext r
    simp only [Poly.part_send, Poly.part_plus]
    split <;> simp
  map_smul' c f := by
    ext r
    simp only [Poly.part_send, Poly.part_smul, RingHom.id_apply]
    split <;> simp
  cont := (Bands.sends q).comp (Poly.part_cont q)

@[simp] theorem modeProjection_apply (q : R.Mode) (f : Poly R) :
    modeProjection q f = Poly.send q (f.part q) := rfl

@[simp] theorem norm_modeProjection (q : R.Mode) (f : Poly R) :
    ‖modeProjection q f‖ = ‖f.part q‖ := by
  change ‖(Pi.single q (f.part q) : R.Mode → ℂ)‖ = _
  exact Pi.norm_single _

abbrev Key (J : Type*) (R : Census V) := Article.Key J R

section Series
variable {J : Type*} {f : J → Poly R}

set_option maxHeartbeats 800000 in
/-- Finite coefficient expansion preserves the given countable sum. -/
theorem key_summable (hf : Summable f) :
    Summable (fun k : Key J R => modeProjection k.2.val (f k.1)) := by
  have hq (q : {q : R.Mode // q ≠ R.quiet}) :
      Summable (fun j => ‖modeProjection q.val (f j)‖) := by
    have hc := ((Poly.get q.val).summable hf).norm
    change Summable (fun j => ‖(f j).part q.val‖) at hc
    simpa only [norm_modeProjection] using hc
  have hp : Summable (fun k : {q : R.Mode // q ≠ R.quiet} × J =>
      modeProjection k.1.val (f k.2)) := by
    apply Summable.of_norm
    exact (summable_prod_of_nonneg
      (f := fun k : {q : R.Mode // q ≠ R.quiet} × J =>
        ‖modeProjection k.1.val (f k.2)‖) (fun _ => norm_nonneg _)).mpr
      ⟨hq, Summable.of_finite⟩
  exact hp.comp_injective (i := fun k : Key J R => (k.2, k.1))
    (Equiv.prodComm J {q : R.Mode // q ≠ R.quiet}).injective

theorem key_tsum (hf : Summable f) :
    (∑' k : Key J R, modeProjection k.2.val (f k.1)) =
      (∑' j, f j) - modeProjection R.quiet (∑' j, f j) := by
  rw [(key_summable hf).tsum_prod]
  simp_rw [tsum_fintype, modeProjection_apply, Article.record_sum]
  change tsum (fun j : J => f j - modeProjection R.quiet (f j)) = _
  rw [hf.tsum_sub ((modeProjection R.quiet).summable hf),
    ← (modeProjection R.quiet).map_tsum hf]
  simp only [modeProjection_apply]

end Series

section Coding
variable {J : Type*} [Countable J]

/-- Padding has zero coefficient; its mode is explicit and does not invent
a member of a possibly empty marker alphabet. -/
def codedMode (fallback : R.Mode) : ℕ → R.Mode :=
  unpin (fun k : Key J R => k.2.val) fallback

def codedCoefficient (f : J → Poly R) : ℕ → ℂ :=
  unpin (fun k : Key J R => (f k.1).part k.2.val) 0

def codedTerm (fallback : R.Mode) (f : J → Poly R) (i : ℕ) : Poly R :=
  Poly.send (codedMode (J := J) fallback i) (codedCoefficient f i)

@[simp] theorem codedTerm_pin (fallback : R.Mode) (f : J → Poly R)
    (k : Key J R) :
    codedTerm fallback f (pin k) = modeProjection k.2.val (f k.1) := by
  simp only [codedTerm, codedMode, codedCoefficient, unpin_pin, modeProjection_apply]

theorem codedTerm_blank (fallback : R.Mode) (f : J → Poly R) {i : ℕ}
    (hi : i ∉ Set.range (pin : Key J R → ℕ)) :
    codedTerm fallback f i = 0 := by
  simp only [codedTerm, codedCoefficient, unpin_blank _ _ hi, Poly.send_zero]

theorem coded_summable (fallback : R.Mode) {f : J → Poly R}
    (hf : Summable f) : Summable (codedTerm fallback f) := by
  have hs : Summable (fun k : Key J R => codedTerm fallback f (pin k)) := by
    simpa only [codedTerm_pin] using key_summable hf
  exact (pin_injective.summable_iff
    (fun i hi => codedTerm_blank fallback f hi)).mp hs

theorem coded_tsum (fallback : R.Mode) {f : J → Poly R}
    (hf : Summable f) :
    (∑' i, codedTerm fallback f i) =
      (∑' j, f j) - modeProjection R.quiet (∑' j, f j) := by
  have he := Push.Corrected.Pad.sums (pin : Key J R → ℕ) pin_injective
    (fun k : Key J R => modeProjection k.2.val (f k.1))
    (codedTerm fallback f) (codedTerm_pin fallback f) (by
      intro i hi
      by_contra hn
      exact hi (codedTerm_blank fallback f hn))
  exact he.symm.trans (key_tsum hf)

def selectedTerm (E : Key J R → Prop) (fallback : R.Mode)
    (f : J → Poly R) (i : ℕ) : Poly R :=
  Poly.send (unpin (fun k : {k : Key J R // E k} => k.val.2.val) fallback i)
    (unpin (fun k : {k : Key J R // E k} => (f k.val.1).part k.val.2.val) 0 i)

@[simp] theorem selectedTerm_pin (E : Key J R → Prop) (fallback : R.Mode)
    (f : J → Poly R) (k : {k : Key J R // E k}) :
    selectedTerm E fallback f (pin k) = modeProjection k.val.2.val (f k.val.1) := by
  simp only [selectedTerm, unpin_pin, modeProjection_apply]

theorem selectedTerm_blank (E : Key J R → Prop) (fallback : R.Mode)
    (f : J → Poly R) {i : ℕ}
    (hi : i ∉ Set.range (pin : {k : Key J R // E k} → ℕ)) :
    selectedTerm E fallback f i = 0 := by
  simp only [selectedTerm, unpin_blank _ _ hi, Poly.send_zero]

theorem selected_summable (E : Key J R → Prop) (fallback : R.Mode)
    {f : J → Poly R} (hf : Summable f) :
    Summable (selectedTerm E fallback f) := by
  have hs : Summable (fun k : {k : Key J R // E k} =>
      modeProjection k.val.2.val (f k.val.1)) :=
    (key_summable hf).comp_injective Subtype.val_injective
  apply (pin_injective.summable_iff
    (fun i hi => selectedTerm_blank E fallback f hi)).mp
  simpa only [Function.comp_def, selectedTerm_pin] using hs

/-- Static omission is exact only with a zero-coefficient receipt for
every omitted label/mode pair. -/
theorem selected_tsum (E : Key J R → Prop) (fallback : R.Mode)
    {f : J → Poly R} (hf : Summable f)
    (hz : ∀ k : Key J R, ¬ E k → (f k.1).part k.2.val = 0) :
    (∑' i, selectedTerm E fallback f i) =
      (∑' j, f j) - modeProjection R.quiet (∑' j, f j) := by
  have hpin := Push.Corrected.Pad.sums
    (pin : {k : Key J R // E k} → ℕ) pin_injective
    (fun k : {k : Key J R // E k} => modeProjection k.val.2.val (f k.val.1))
    (selectedTerm E fallback f) (selectedTerm_pin E fallback f) (by
      intro i hi
      by_contra hn
      exact hi (selectedTerm_blank E fallback f hn))
  have hsub := Push.Corrected.Pad.sums
    (Subtype.val : {k : Key J R // E k} → Key J R) Subtype.val_injective
    (fun k : {k : Key J R // E k} => modeProjection k.val.2.val (f k.val.1))
    (fun k : Key J R => modeProjection k.2.val (f k.1)) (fun _ => rfl) (by
      intro k hk
      have hE : E k := by
        by_contra hn
        apply hk
        simp only [modeProjection_apply, hz k hn, Poly.send_zero]
      exact ⟨⟨k, hE⟩, rfl⟩)
  exact hpin.symm.trans (hsub.trans (key_tsum hf))

end Coding

/- The raw label tables precede masking, summation and norm evaluation.
   A native Manor/Yard supplies them without a new analytic assumption. -/
structure Ledger (Ω J : Type*) (G : Gauge) (n : Side) (R : Census V) where
  region : J → Support n
  raw : Ω → J → Config G n → Poly R
  total : J → Prop
  forced : Ω → ℕ → Config G n → Poly R

namespace Ledger
variable {Ω J : Type*} [Countable J] {G : Gauge} {n : Side}
    (L : Ledger Ω J G n R) (P : Rep G n) (o : V → Site n)

def covered (span : V → Support n) (k : Key J R) : Prop :=
  ∀ v ∈ k.2.val.val, span v ⊆ L.region k.1

/-- Only modes covered by the original label's full declared test regions
are materialized. Zero padding uses the full lattice. -/
abbrev RegularKey (span : V → Support n) :=
  {k : Key J R // L.covered span k}

def article (a : Ω) : Article ℕ P.p G R o where
  address := P.activities.forced
  flow := L.forced a

section Marked
variable [Nonempty V] (span : V → Support n)

def view : View Ω V G n P R where
  origins := o
  rays := unpin (fun k : L.RegularKey span => k.val.2.val) (R.fire (Classical.arbitrary V))
  branch := unpin (fun k : L.RegularKey span => L.region k.val.1) Finset.univ
  marks _ := codedMode (J := ℕ) (R.fire (Classical.arbitrary V))
  global _ _ := 0
  regular a := unpin (fun k : L.RegularKey span => fun U =>
    if L.total k.val.1 then 0 else (L.raw a k.val.1 U).part k.val.2.val) 0
  force a i := unpin (fun k : Key ℕ R => fun U =>
    if k.1 = i then (L.forced a k.1 U).part k.2.val else 0) 0

def taste : Taste Ω o P R where
  menu := L.view P o span
  root := rfl
  tag := unpin (fun k : L.RegularKey span => k.val.2.val) (R.fire (Classical.arbitrary V))
  site := unpin (fun k : L.RegularKey span => L.region k.val.1) Finset.univ
  score a := unpin (fun k : L.RegularKey span =>
    if L.total k.val.1 then (L.raw a k.val.1 1).part k.val.2.val else 0) 0

@[simp] theorem regular_mode (k : L.RegularKey span) :
    (L.taste P o span).menu.rays (pin k) = k.val.2.val := by
  simp only [taste, view, unpin_pin]

@[simp] theorem regular_region (k : L.RegularKey span) :
    (L.taste P o span).menu.branch (pin k) = L.region k.val.1 := by
  simp only [taste, view, unpin_pin]

@[simp] theorem caption_region (k : L.RegularKey span) :
    (L.taste P o span).site (pin k) = L.region k.val.1 := by
  simp only [taste, unpin_pin]

theorem regular_covers (i : ℕ) (v : V)
    (hv : v ∈ ((L.taste P o span).menu.rays i).val) :
    span v ⊆ (L.taste P o span).menu.branch i := by
  by_cases hc : i ∈ Set.range (pin : L.RegularKey span → ℕ)
  · obtain ⟨k, rfl⟩ := hc
    rw [regular_region]
    exact k.property v (by simpa only [regular_mode] using hv)
  · simp only [taste, view, unpin_blank _ _ hc]
    exact Finset.subset_univ _

theorem caption_covers (i : ℕ) (v : V)
    (hv : v ∈ ((L.taste P o span).tag i).val) :
    span v ⊆ (L.taste P o span).site i :=
  L.regular_covers P o span i v hv

/-- The forced half is exactly the existing native `Article.impression`
with identity routing onto the original carrier's forced slots. -/
theorem native_impression (a : Ω) :
    (L.article P o a).impression ((L.taste P o span).menu.terms a) id =
      (L.taste P o span).menu.terms a := rfl

/-- Routing is fixed before choosing tests or a field configuration. -/
def forceRouted (i j : ℕ) : Prop :=
  ∃ k : Key ℕ R, pin k = j ∧ k.1 = i

/-- The declaration uses the full original test regions, not pointwise
nonvanishing of a coefficient. -/
def forceDeclared (i j : ℕ) : Prop :=
  ∃ k : Key ℕ R, pin k = j ∧ k.1 = i ∧
    ∀ v ∈ k.2.val.val, span v ⊆ (P.activities.forced i).support

theorem forced_source (a : Ω) (i : ℕ)
    (q : {q : R.Mode // q ≠ R.quiet}) (U : Config G n) :
    (L.taste P o span).menu.force a i (pin ((i, q) : Key ℕ R)) U =
      (L.forced a i U).part q.val := by
  simp [taste, view]

theorem forced_offRoute (a : Ω) (i j : ℕ) (U : Config G n)
    (h : ¬ forceRouted (R := R) i j) :
    (L.taste P o span).menu.force a i j U = 0 := by
  by_cases hc : j ∈ Set.range (pin : Key ℕ R → ℕ)
  · obtain ⟨k, rfl⟩ := hc
    have hi : k.1 ≠ i := fun hi => h ⟨k, rfl, hi⟩
    simp only [taste, view, unpin_pin, if_neg hi]
  · simp only [taste, view, unpin_blank _ _ hc, Pi.zero_apply]

theorem forced_offDeclaration
    (hg : ∀ a i U q, (L.forced a i U).part q ≠ 0 →
      ∀ v ∈ q.val, span v ⊆ (P.activities.forced i).support)
    (a : Ω) (i j : ℕ) (U : Config G n)
    (h : ¬ forceDeclared (R := R) P span i j) :
    (L.taste P o span).menu.force a i j U = 0 := by
  by_cases hc : j ∈ Set.range (pin : Key ℕ R → ℕ)
  · obtain ⟨k, rfl⟩ := hc
    by_cases hi : k.1 = i
    · by_contra hn
      apply h
      refine ⟨k, rfl, hi, ?_⟩
      subst i
      apply hg a k.1 U k.2.val
      simpa [taste, view] using hn
    · simp only [taste, view, unpin_pin, if_neg hi]
  · simp only [taste, view, unpin_blank _ _ hc, Pi.zero_apply]

/-- Each forced fibre reconstructs the whole original polynomial. Its
quiet coefficient remains the existing physical carrier's `K`. -/
theorem forced_each (a : Ω) (i : ℕ) (U : Config G n)
    (hq : (L.forced a i U).part R.quiet = (P.activities.K i U : ℂ)) :
    ((L.taste P o span).menu.terms a).each i U = L.forced a i U := by
  let f (j : ℕ) := if j = i then L.forced a j U else 0
  have hs : Summable f :=
    (hasSum_single i (fun j hj => show f j = 0 by simp only [f, if_neg hj])).summable
  have he (j : ℕ) :
      ((L.taste P o span).menu.terms a).tagged i j U =
        codedTerm (R.fire (Classical.arbitrary V)) f j := by
    by_cases hc : j ∈ Set.range (pin : Key ℕ R → ℕ)
    · obtain ⟨k, rfl⟩ := hc
      rw [codedTerm_pin]
      simp only [Bands.tagged, View.terms, taste, view, codedMode, unpin_pin]
      by_cases hi : k.1 = i <;>
        simp only [f, hi, if_true, if_false, modeProjection_apply, Poly.part_nil]
    · rw [codedTerm_blank _ _ hc]
      simp only [Bands.tagged, View.terms, taste, view, unpin_blank _ _ hc,
        Pi.zero_apply, Poly.send_zero]
  unfold Bands.each
  rw [tsum_congr he, coded_tsum _ hs]
  have hf : (∑' j, f j) = L.forced a i U := by
    exact tsum_ite_eq i (fun j => L.forced a j U)
  rw [hf, modeProjection_apply, hq]
  abel

theorem forced_cluster (a : Ω) (U : Config G n)
    (hq : ∀ i, (L.forced a i U).part R.quiet = (P.activities.K i U : ℂ)) :
    ((L.taste P o span).menu.terms a).cluster U =
      ∑' l : Finset ℕ, if P.activities.admissible P.p U l then
        ∏ i ∈ l, L.forced a i U else 0 := by
  apply tsum_congr
  intro l
  unfold Bands.packet
  split_ifs
  · apply Finset.prod_congr rfl
    intro i _
    exact L.forced_each P o span a i U (hq i)
  · rfl

variable {I : Type} [DecidableEq I] (B : Layout I V)

/-- Support is required and used on each original polynomial label.
No support property of a completed sum is substituted for these receipts. -/
theorem blockPresentation
    (hr : ∀ a j U, B.Supported (L.raw a j U))
    (hf : ∀ a i U, B.Supported (L.forced a i U)) :
    LocalComparison.BlockPresentation B (L.taste P o span) := by
  constructor
  · intro v _ a
    rfl
  · intro i hi a U
    by_cases hc : i ∈ Set.range (pin : L.RegularKey span → ℕ)
    · obtain ⟨k, rfl⟩ := hc
      simp only [taste, view, unpin_pin] at hi ⊢
      split_ifs
      · rfl
      · exact hr a k.val.1 U k.val.2.val hi
    · simp only [taste, view, unpin_blank _ _ hc, Pi.zero_apply]
  · intro i j hj a U
    by_cases hc : j ∈ Set.range (pin : Key ℕ R → ℕ)
    · obtain ⟨k, rfl⟩ := hc
      simp only [taste, view, codedMode, unpin_pin] at hj ⊢
      split_ifs
      · exact hf a k.1 U k.2.val hj
      · rfl
    · simp only [taste, view, unpin_blank _ _ hc, Pi.zero_apply]
  · intro i hi a
    by_cases hc : i ∈ Set.range (pin : L.RegularKey span → ℕ)
    · obtain ⟨k, rfl⟩ := hc
      simp only [taste, unpin_pin] at hi ⊢
      split_ifs
      · exact hr a k.val.1 1 k.val.2.val hi
      · rfl
    · simp only [taste, unpin_blank _ _ hc]

end Marked
end Ledger

end YM.Integration.RiderTastePresentation
