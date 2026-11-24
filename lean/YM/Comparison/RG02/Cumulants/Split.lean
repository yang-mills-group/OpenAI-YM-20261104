import YM.Comparison.RG02.Cumulants.Partition

/-!
# Factorization and connectedness

Dependency relation may include more than just covariance lines (in particular all common tags
read by factors). **Only** if the joint-weight calculation factorizes along the candidate cut do
we cancel. Work anywhere in the Census so this applies to conditionally chosen costs at ANY finite
load even when no consistent estimates assigned to other pieces, or under further insertion and log
substitution. No independence assumption on general inputs to the matching theorem.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Comparison.RG02.Cumulants
open YM.Marker YM.Multi YM.Primitives.GCC.Anchor
open YM.Extra.Trajectories (connected connected_quiet pass_connected part_sub)
open Finset
open scoped BigOperators Classical

variable {V : Type*} [DecidableEq V] {R : Census V}

/-- Counts inside the permitted window U. -/
def inside (s : R.Mode) (U : Finset V) : R.Mode := ⟨s.val ∩ U, R.down s.property _ inter_subset_left⟩
lemma merges_side (s : R.Mode) (U : Finset V) : Poly.merges (inside s U) (diff s U) s := by
  change Disjoint _ _ ∧ s.val ∩ U ∪ (s.val \ U) = s.val
  exact ⟨disjoint_left.mpr fun _ ha hb => (mem_sdiff.mp hb).2 (mem_inter.mp ha).2, (Finset.union_comm ..).trans (sdiff_union_inter ..)⟩
lemma inside_forced {s a b : R.Mode} {U : Finset V}
    (h : Poly.merges a b s) (ha : a.val⊆U) (hb : Disjoint b.val U) : inside s U = a := by
  apply Subtype.ext
  change s.val ∩ U=a.val; rw [← h.2, Finset.union_inter_distrib_right,
    Finset.inter_eq_left.mpr ha, Finset.disjoint_iff_inter_eq_empty.mp hb, Finset.union_empty]
lemma diff_forced {s a b : R.Mode} {U : Finset V}
    (h : Poly.merges a b s) (ha : a.val⊆U) (hb : Disjoint b.val U) : diff s U = b := by
  trans diff s a.val
  · rw [← separates_unique s a (diff s U)]; rw [← inside_forced h ha hb]; exact merges_side ..
  exact (separates_unique s a b h).symm

/-- Each side may come from a single table (cancellation criterion below), or distinct. -/
lemma part_split (U : Finset V) (x y : Poly R) (s : R.Mode) :
    (withinSet U x * without U y).part s = x.part (inside s U) * y.part (diff s U) := by
  rw [Poly.part_mul, Finset.sum_eq_single (inside s U), Finset.sum_eq_single (diff s U)]
  · rw [if_pos (merges_side s U)]; change (if _ then x.part _ else 0)*(if _ then y.part _ else 0)=_
    rw [if_pos (show (inside s U).val ⊆ U from inter_subset_right),
      if_pos (show Disjoint (diff s U).val U from ?_)]
    exact disjoint_left.mpr fun _ ha => (mem_sdiff.mp ha).2
  · intro a _ ha
    rw [if_neg]; intro hm; exact ha ( (separates_unique _ _ _ hm).trans (separates_unique _ _ _ (merges_side s U)).symm)
  · simp
  · intro a _ ha; refine sum_eq_zero fun b _ => ?_
    split
    next hm =>
      change (if a.val ⊆ U then x.part a else 0)*(if Disjoint b.val U then y.part b else 0)=0
      split_ifs with h h' h' <;> first | exact False.elim (ha (inside_forced hm h h').symm) | simp
    next => rfl
  simp

lemma begin_inner_part (U : Finset V) (x : Poly R) (s) :
    (withinSet U x).part s = if s.val ⊆ U then x.part s else 0 := rfl
lemma begin_outer_part (U : Finset V) (x : Poly R) (s) :
    (without U x).part s = if Disjoint s.val U then x.part s else 0 := rfl

-- projections as special dilations (preserves global marks assigned to surviving slots only)
lemma dilation_scope (x : Poly R) (U : Finset V) :
    withinSet U x = dilation R (fun i => if i∈U then 1 else 0) x := by
  ext s
  rw [begin_inner_part, dilation_part]
  split
  next h => rw [prod_eq_one (fun i hi=> if_pos (h hi)),one_mul]
  next h =>
    obtain ⟨i,hi,he⟩ := not_subset.mp h
    rw [prod_eq_zero hi (if_neg he),zero_mul]
lemma dilation_outside (x : Poly R) (U : Finset V) :
    without U x = dilation R (fun i => if i∈U then 0 else 1) x := by
  ext s
  rw [begin_outer_part, dilation_part]
  split
  next h => rw [prod_eq_one (fun i hi=> if_neg (fun he => disjoint_left.mp h hi he)),one_mul]
  next h =>
    obtain ⟨i,hi,he⟩ := not_disjoint_iff.mp h
    rw [Finset.prod_eq_zero (f:=fun i=> if i∈U then (0:ℂ) else 1) hi (if_pos he),zero_mul]
lemma quiet_dilation (f : V → ℂ) (x : Poly R) :
    (dilation R f x).part R.quiet = x.part R.quiet := by
  simp [dilation_part,Census.quiet]

section
variable [Fintype V]
lemma conn_inside (U : Finset V) (x : Poly R) (hx : x.part R.quiet=1) :
    connected (withinSet U x)=withinSet U (connected x) := by
  simp_rw [dilation_scope]; exact Eq.symm (log_map _ (quiet_dilation _) hx)
lemma conn_outside (U : Finset V) (x : Poly R) (hx : x.part R.quiet=1) :
    connected (without U x)=without U (connected x) := by
  simp_rw [dilation_outside]; exact Eq.symm (log_map _ (quiet_dilation _) hx)

lemma conn_split (U : Finset V) (x : Poly R) (hx : x.part R.quiet=1) (t : Finset V)
    (he : ∀ s : R.Mode, s.val ⊆ t → x.part s=x.part (inside s U)*x.part (diff s U)) :
    UpTo t (connected x) (withinSet U (connected x) + without U (connected x)) := by
  have h : UpTo t x ((withinSet U x) * without U x) := fun i hi =>
    (he i hi).trans (part_split U x x i).symm
  rw [← conn_inside U x hx,← conn_outside U x hx,← connected_mul];
  · exact h.conn
  · rwa [dilation_scope,quiet_dilation]
  · rwa [dilation_outside,quiet_dilation]

/-- All-component coefficient cancels at a cut. Applies recursively (e.g., outer tag cumulants
    of an already Wick-connected selection). **Reads actual weights** (via parts), not graph
    structure alone. -/
lemma conn_crossing (U : Finset V) (x : Poly R) (hx : x.part R.quiet=1) (t : R.Mode)
    (he : ∀ s : R.Mode, s.val ⊆ t.val → x.part s=x.part (inside s U)*x.part (diff s U))
    (hi : (inside t U).val.Nonempty) (ho : (diff t U).val.Nonempty) :
    (connected x).part t = 0 := by
  obtain ⟨i,hi⟩:=hi; obtain ⟨j,hj⟩:=ho
  rw [conn_split U x hx t.val he t (Subset.refl _), Poly.part_plus,
    begin_inner_part, begin_outer_part];
  have ht : ¬ t.val⊆U := fun h=> (mem_sdiff.mp hj).2 (h (mem_sdiff.mp hj).1)
  have he : ¬ Disjoint t.val U := not_disjoint_iff.mpr ⟨i,(mem_inter.mp hi).1,(mem_inter.mp hi).2⟩
  rw [if_neg ht, if_neg he]; simp

end
end YM.Comparison.RG02.Cumulants
