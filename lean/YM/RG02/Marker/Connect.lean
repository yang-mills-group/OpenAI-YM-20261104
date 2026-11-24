import YM.RG02.Marker.Euler
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Algebra

/-!
# Connectivity and exact cumulant vanishing

A cut criterion, with the entire moment test made on one restricted
(maybe geometric) census. 'No split' connectivity avoids throwing out
intersections at a single tag/link, works also for single-vertex terms.
In applications to the tag law, `u` may be separated from the rest when
no dependency crosses the cut; any shared *physical* tag still connects,
and after interacting weighting also the vacuum/normalizer must satisfy the
factorization before this criterion applies.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG02.Marks
open Finset Marker Extra.Trajectories Primitives.GCC.Anchor
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι] {R : Census ι}

def inside (u : Finset ι) (s : R.Mode) : R.Mode := ⟨s.val ∩ u, R.down s.property _ inter_subset_left⟩
def outside (u : Finset ι) (s : R.Mode) : R.Mode := ⟨s.val \ u, R.down s.property _ sdiff_subset⟩

/-- Multiplicative splitting inside one subcensus. This is a statement
about the *numerical moments*; no implicit independence. -/
def Divides (x : Poly R) (u v : Finset ι) : Prop :=
  ∀ s : R.Mode, s.val ⊆ v → x.part s = x.part (inside u s) * x.part (outside u s)

private lemma cut_merge (u : Finset ι) (s : R.Mode) : Poly.merges (inside u s) (outside u s) s := by
  refine ⟨(Finset.disjoint_left.mpr ?_),by dsimp [inside,outside]; ext; grind⟩
  exact fun i hi hh => (mem_sdiff.mp hh).2 (mem_inter.mp hi).2

theorem factor_entry (x : Poly R) (u : Finset ι) (s : R.Mode) :
    (withinSet u x * without u x).part s = x.part (inside u s)*x.part (outside u s) := by
  have hl (b : R.Mode) : (withinSet u x).part b = if b.val ⊆ u then x.part b else 0 := rfl
  have hr (b : R.Mode) : (without u x).part b = if Disjoint b.val u then x.part b else 0 := rfl
  have he (a b : R.Mode) (h : Poly.merges a b s) (ha : a.val ⊆ u) (hb : Disjoint b.val u) :
      a = inside u s ∧ b = outside u s := by
    have h' := h.2
    constructor
    · apply Subtype.ext; unfold inside; dsimp only; rw [← h', union_inter_distrib_right, inter_eq_left.mpr ha, Finset.disjoint_iff_inter_eq_empty.mp hb, union_empty]
    apply Subtype.ext; unfold outside; dsimp only
    rw [← h',union_sdiff_distrib,sdiff_eq_empty_iff_subset.mpr ha,sdiff_eq_self_of_disjoint hb,empty_union]
  rw [Poly.part_mul,sum_eq_single (inside u s), sum_eq_single (outside u s)]
  · rw [if_pos (cut_merge u s), hl, hr]
    rw [if_pos (show (inside u s).val ⊆ u from inter_subset_right),
      if_pos (show Disjoint (outside u s).val u from disjoint_left.mpr fun j h => (mem_sdiff.mp h).2)]
  · intro b _ hn
    by_cases h : Poly.merges (inside u s) b s
    · rw [if_pos h, hr, if_neg (fun H => hn (he _ _ h inter_subset_right H).2),mul_zero]
    exact if_neg h
  · simp
  · intro a _ hn
    apply sum_eq_zero; intro b _
    by_cases h : Poly.merges a b s
    · rw [if_pos h]
      by_cases ha : a.val ⊆ u
      · rw [hr, if_neg (fun H => hn (he _ _ h ha H).1), mul_zero]
      rw [hl, if_neg ha,zero_mul]
    exact if_neg h
  simp

theorem divides_iff (x : Poly R) (u v : Finset ι) :
    Divides x u v ↔ UpTo v x (withinSet u x * without u x) := by simp [Divides,UpTo,factor_entry]

lemma lacks_iff {i : ι} {x : Poly R} : Lacks i x ↔ euler i x = 0 := by
  constructor
  · intro h; ext s
    rw [part_euler,Poly.part_nil]; split
    next hv => exact h s hv
    rfl
  intro h s hs
  rw [← if_pos hs (t:=x.part s) (e:=0), ← part_euler, h, Poly.part_nil]

/-- No bipartition without a dependence crossing. Pass in a symmetric
criterion, e.g. intersection of layers or a Wick line crossing. Holds also
when same mark position or label is used in many factors. -/
def NoCut (v : Finset ι) (E : ι → ι → Prop) :=
  ∀ u ⊆ v, u.Nonempty → (v\u).Nonempty → ∃ i∈u, ∃ j∈v\u, E i j

variable [Fintype ι]

lemma lacks_connected {i : ι} {x : Poly R} (hx : x.part R.quiet=1) (h : Lacks i x) :
    Lacks i (connected x) := by
  rw [lacks_iff] at h ⊢
  apply (unit_of_quiet_one hx).mul_right_inj.mp
  rw [← euler_connected hx i,h,mul_zero]

/-- Hold only this subset of actually permitted insertions. Splitting
some larger or unrelated mask is not required. -/
theorem connected_vanish {x : Poly R} (hx : x.part R.quiet = 1)
    {u : Finset ι} (s : R.Mode) (h1 : (u ∩ s.val).Nonempty) (h2 : (s.val\u).Nonempty)
    (he : Divides x u s.val) : (connected x).part s = 0 := by
  obtain ⟨i,hi⟩ := h1; obtain ⟨j,hj⟩ := h2
  have hI := mem_inter.mp hi
  have hJ := mem_sdiff.mp hj
  let a := withinSet u x
  let b := without u x
  have ha : a.part R.quiet=1 := by change (if R.quiet.val ⊆ u then x.part R.quiet else 0)=1; rw [if_pos (by simp [Census.quiet])]; exact hx
  have hb : b.part R.quiet=1 := by change (if Disjoint R.quiet.val u then x.part R.quiet else 0)=1; rw [if_pos (by simp [Census.quiet])]; exact hx
  have hj : Lacks j a := fun s H => if_neg (fun (e : s.val ⊆ u) => hJ.2 (e H))
  have hi : Lacks i b := fun s H => if_neg (fun (e : Disjoint s.val u) => disjoint_left.mp e H hI.1)
  rw [show (connected x).part s=(connected (a*b)).part s from ((divides_iff ..).mp he).conn s subset_rfl,
    connected_mul ha hb,Poly.part_plus, lacks_connected ha hj s hJ.1, lacks_connected hb hi s hI.2,add_zero]

/-- A nonzero cumulant must be connected, provided the dependency relation
is conservative for factorization at this fixed mode. -/
theorem connected_must_link {x : Poly R} (hx : x.part R.quiet=1) (s : R.Mode)
    (E : ι → ι → Prop)
    (H : ∀ u ⊆ s.val, (∀ i∈u, ∀ j∈s.val\u, ¬ E i j) → Divides x u s.val)
    (h : (connected x).part s ≠ 0) : NoCut s.val E := by
  intro u hu he hf
  by_contra! hn
  apply h
  exact connected_vanish hx s (by rwa [inter_eq_left.mpr hu]) hf (H u hu hn)
end YM.RG02.Marks
