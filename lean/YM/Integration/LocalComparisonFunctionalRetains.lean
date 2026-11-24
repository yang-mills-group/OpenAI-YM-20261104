import YM.Integration.LocalComparisonInterface

/-!
# Locality for nonzero complete marked functionals

A zero padded forced coefficient still has a nonempty mark set in the native
Active representation. Requiring that coefficient's insertion address in every
original vacuum support would exclude an otherwise admissible distant vacuum
polymer. The condition below ignores only coefficients identically zero for
ALL independent tests and fields. It does not select a layout at a later test.

The original Taste, vacuum carrier, flags, values, and weighted norm are not
changed. No representation rebooking or new norm estimate is asserted here.
Larger stencil-address sets still require their own support proof. The original
unconditional Retains remains available as a strictly stronger receipt.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison

open Lattice Wilson RG Marker
open RG3.Held RG3.Forms RG3.Script.Picnic
open scoped Classical

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
    {R : Census V} {X : Type*} {P : Rep G n} {o : V → Site n}
    {T : Taste X o P R} {address : V → Support n}

/-- Locality of every nonzero coefficient of the whole test functional.
The existential tests only whether a fixed row is identically zero; the
support assertion then applies to every marked slot of that same row. -/
structure FunctionalRetains (T : Taste X o P R)
    (address : V → Support n) : Prop where
  origins v : o v ∈ address v
  regular i v : (∃ x U, T.menu.regular x i U ≠ 0) →
    v ∈ (T.menu.rays i).val → address v ⊆ T.menu.branch i
  forced i j v : (∃ x U, T.menu.force x i j U ≠ 0) →
    v ∈ (T.menu.marks i j).val → address v ⊆ (P.activities.forced i).support
  captions i v : (∃ x, T.score x i ≠ 0) →
    v ∈ (T.tag i).val → address v ⊆ T.site i

/-- The old unconditional receipt implies whole-functional locality. -/
theorem Retains.functional (h : Retains T address) : FunctionalRetains T address where
  origins := h.origins
  regular i v _ := h.regular i v
  forced i j v _ := h.forced i j v
  captions i v _ := h.captions i v

/-- Native activity gives this locality for the original singleton origins.
It does not give retention of an enlarged stencil-address set. -/
theorem FunctionalRetains.of_active (h : ∀ x, (T.leaf x).Active) :
    FunctionalRetains T (fun v => {o v}) := by
  refine ⟨fun _ => Finset.mem_singleton_self _, ?_, ?_, ?_⟩
  · intro i v hn hv z hz
    rcases hn with ⟨x, U, _⟩
    have hp := (h x).articles.pins i v hv
    have he : z = o v := Finset.mem_singleton.mp hz
    subst z
    simpa only [Taste.leaf, View.terms, T.root] using hp
  · intro i j v hn hv z hz
    rcases hn with ⟨x, U, hU⟩
    have hne : (T.leaf x).contents.entries i j ≠ 0 := by
      intro he
      apply hU
      exact congrFun he U
    have hp := (h x).articles.retained i j hne v hv
    have he : z = o v := Finset.mem_singleton.mp hz
    subst z
    simpa only [Taste.leaf, View.terms, T.root] using hp
  · intro i v hn hv z hz
    rcases hn with ⟨x, _⟩
    have hp := (h x).captions.pins i v hv
    have he : z = o v := Finset.mem_singleton.mp hz
    subst z
    simpa only [Taste.leaf, View.terms, T.root] using hp

/-- In one tag, unconditional Retains forces every vacuum forced support to
contain its insertion address, even when that marked coefficient is zero. -/
theorem Retains.all_forced_of_subsingleton [Subsingleton V]
    (h : Retains T address) (x : X) (hActive : (T.leaf x).Active)
    (v : V) (i : ℕ) : address v ⊆ (P.activities.forced i).support := by
  obtain ⟨u, hu⟩ := hActive.articles.occurs i 0
  have he : u = v := Subsingleton.elim _ _
  subst u
  exact h.forced i 0 v hu

/-- A distant original vacuum support therefore obstructs that stronger
receipt. This is not an obstruction to the nonzero-row formulation. -/
theorem not_retains_of_distant_forced [Subsingleton V]
    (x : X) (hActive : (T.leaf x).Active) (v : V) (i : ℕ)
    (hMissing : o v ∉ (P.activities.forced i).support) :
    ¬ Retains T address := by
  intro h
  exact hMissing (h.all_forced_of_subsingleton x hActive v i (h.origins v))

end YM.Integration.LocalComparison
