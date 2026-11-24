import YM.FormalOPE.RG10.Rooting

/-! Native subset algebra, useful when geometry singles out a marker and also for low-order
agreement. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10
open Marker Extra.Trajectories PowerSeries MeasureTheory Finset Primitives.GCC Function
open scoped BigOperators

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
namespace Word

omit [Fintype V] in
/-- Sum just over the left factor's support. -/
lemma scanning (A B : Word R) (s : R.Mode) :
    see s (A*B) = ∑ a, if a.val ⊆ s.val then see a A * see (Anchor.diff s a.val) B else 0 := by
  rw [convolves]; apply Finset.sum_congr rfl; intro a _; split <;> rename_i h
  · rw [Finset.sum_eq_single (Anchor.diff s a.val)];
    · rw [if_pos (Anchor.separates _ _ h)]
    · intro x hx hX; rw [if_neg]; exact fun hz => hX (Anchor.separates_unique s a x hz)
    simp
  exact Finset.sum_eq_zero fun v _ => if_neg (fun hm : Poly.merges a v s => h (hm.2 ▸ Finset.subset_union_left))

/-- Rooted, unnormalized-with-respect-to-coupling version, valid with `boot = 1`. Input `A`
is the *ordinary* complete moment. For a mark in `s`, read its coefficient by splitting over
ways its connected piece attaches to the rest. No summing over unaligned positions, masks or
tag choices. -/
theorem assembled {A : Word R} (h : boot A = 1) (s : R.Mode) {i} (hi : i∈s.val) :
    see s A = ∑ a : R.Mode, if a.val ⊆ s.val ∧ i∈a.val then
      see a (logWord A) * see (Anchor.diff s a.val) A else 0 := by
  have he := congr_arg (see s) (adjoin i A h)
  rw [leaf_pick, if_pos hi, scanning] at he
  apply he.trans; apply sum_congr rfl; intro a _
  rw [leaf_pick]; by_cases h': a.val ⊆ s.val <;> by_cases h'':i∈a.val <;> simp [h',h'']

lemma alone (A : Word R) (h : vac R A = 1) (i : V) : see (R.fire i) (logWord A)=see (R.fire i) A := by
  symm; have hb : boot A=1 := by unfold boot; rw [h]; simp
  rw (occs:=.pos [1]) [assembled hb (R.fire i) (show i∈(R.fire i).val from mem_singleton_self i),
    Finset.sum_eq_single (R.fire i)];
  · rw [if_pos (by simp [Census.fire]), show Anchor.diff (R.fire i) _=R.quiet from Subtype.ext (by simp [Anchor.diff, Census.quiet]), ← vac_eq, h, mul_one]
  · intro v hv hv'; rw [if_neg]
    exact fun he => hv' (Subtype.ext (Finset.Subset.antisymm he.1 (Finset.singleton_subset_iff.mpr he.2)))
  simp

lemma crown (A : Word R) (h : vac R A = 1) (s : R.Mode) {i j : V} (hi : i≠j) (hv : s.val={i,j}) :
    see s (logWord A) = see s A - see (R.fire i) A * see (R.fire j) A := by
  have hb : boot A=1 := by unfold boot; rw [h]; simp
  apply eq_sub_of_add_eq
  symm; rw [assembled hb s (show i∈s.val by rw [hv]; simp), ← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
  congr 1
  · rw [if_pos (by simp [hv]), show Anchor.diff s s.val=R.quiet from Subtype.ext (by simp [Anchor.diff,Census.quiet]), ← vac_eq, h, mul_one]
  have hn : R.fire i ≠ s := fun e => hi.symm (Finset.mem_singleton.mp (show j∈(R.fire i).val by rw [e,hv]; simp))
  rw [Finset.sum_eq_single_of_mem (R.fire i) (mem_erase.mpr ⟨hn,mem_univ _⟩)]
  · rw [if_pos (by simp [hv,Census.fire]), alone A h i, show Anchor.diff s ((R.fire i).val)=R.fire j from
      Subtype.ext (by simp [hv,Census.fire,Anchor.diff,hi, Finset.sdiff_singleton_eq_erase])]
  intro b hb hh; rw [if_neg]; intro hp
  have hsub := hp.1; rw [hv] at hsub
  by_cases he : j∈b.val
  · apply Finset.ne_of_mem_erase hb; apply Subtype.ext (Finset.Subset.antisymm hp.1 ?_)
    rw [hv]; exact insert_subset hp.2 (singleton_subset_iff.mpr he)
  apply hh (Subtype.ext (Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr hp.2)))
  intro k hk; have hL := mem_insert.mp (hsub hk)
  rcases hL with hL|hL
  · exact Finset.mem_singleton.mpr hL
  exact (he ((Finset.mem_singleton.mp hL) ▸ hk)).elim
end Word
end YM.FormalOPE.RG10
