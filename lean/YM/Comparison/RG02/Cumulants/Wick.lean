import YM.Comparison.RG02.Cumulants.TagCut
import YM.Next.RANK.GaussTrack

/-!
# Identify the Gaussian connected cumulants by recursion with labelled contractions.

Work inside `Rank.Normal.blend` -- suppress no diagonals. Words have chosen
**leg occurrences** in addition to vertex markers; may of course have repeated field
indices. Reusable on each **joint** gaussian input, covariance and weights may all depend on
the same reference tags. Every recursion edge of `trees` joining two vertices is paid for by
an actual (off-vertex, possibly same physical position) covariance entry. Thus computes only
connected diagrams; other line contractions cost their genuine entries too (no factor of
`1/2`). `total_log` then connects blocks with respect to the reference tag law. `cumulant_add`,
`cumulant_smul`, `cumulant_sum` allow linearity, in particular expanding vertices after such a
comparison and further expanding that outer tag formula at each chosen block.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Cumulants.Wick
open YM.Next.Rank
open YM.Marker YM.Multi YM.Primitives.GCC.Anchor
open YM.Extra.Trajectories (connected connected_quiet pass_connected)
open Finset
open scoped BigOperators Classical

-- I are leg occurrences. J needn't be finite here; in integral comparisons use realized covariance.
variable {V I J : Type*} [DecidableEq V] [DecidableEq I] {R : Census V}
    (loc : I → V) (idx : I → J)
abbrev legs (p : Finset I) (s : Finset V) : Finset I := p.filter (fun j=> loc j∈s)

def word (p : Finset I) (v : V) := Normal.glyphs idx (legs loc p {v})
lemma filter_erase (p : Finset I) (s : Finset V) (i : I) :
    legs loc (p.erase i) s=(legs loc p s).erase i := Finset.filter_erase ..
lemma all_slots (p : Finset I) (s : Finset V) :
    s.biUnion (fun v=> legs loc p {v}) = legs loc p s := by
  ext j; simp [legs]; tauto
omit [DecidableEq I] in
lemma all_separate (p : Finset I) (s : Finset V) :
    (s : Set V).PairwiseDisjoint (fun v=> legs loc p {v}) := by
  intro i _ j _ he
  apply Finset.disjoint_left.mpr; rintro b hb hv
  exact he (by simp only [legs,mem_filter, mem_singleton] at hb hv; exact hb.2.symm.trans hv.2)
lemma all_word (p : Finset I) (s : Finset V) :
    (∏ i∈s, word loc idx p i) = Normal.glyphs idx (legs loc p s) := by
  rw [← all_slots, Normal.glyphs, Finset.prod_biUnion (all_separate loc p s)]
  rfl

variable (Q : Normal.Symmetric J) (μ : J → ℂ)

abbrev moment (p : Finset I) := moments R (Normal.blend Q μ) (word loc idx p)
omit [DecidableEq I] in
lemma moment_value (s : R.Mode) (p : Finset I) :
    (moment loc idx Q μ p).part s=Normal.blend Q μ (Normal.glyphs idx (legs loc p s.val)) := by
  rw [moment,moments_part,all_word]

lemma moment_no_see (p : Finset I) (i : I) (s : R.Mode) (he : loc i∉s.val) :
    (moment loc idx Q μ p).part s=(moment loc idx Q μ (p.erase i)).part s := by
  rw [moment_value,moment_value,filter_erase, erase_eq_of_notMem _]
  exact fun h=> he (mem_filter.mp h).2

-- Wick spring identity across all present legs after choosing root leg i
lemma moment_remove (s : R.Mode) (p : Finset I) (i : I) (hi : i∈p) (hs : loc i ∈ s.val) :
    (moment loc idx Q μ p).part s =
      μ (idx i)*(moment loc idx Q μ (p.erase i)).part s +
        ∑ j∈p.erase i, if loc j∈s.val then Q.cov (idx i) (idx j)*
          (moment loc idx Q μ ((p.erase i).erase j)).part s else 0 := by
  simp_rw [moment_value, ← sum_filter]
  rw [show legs loc p s.val=insert i (legs loc (p.erase i) s.val) by
    rw [filter_erase, insert_erase (mem_filter.mpr ⟨hi,hs⟩)],
    Normal.spring μ Q idx _ (fun h=> notMem_erase i p (mem_filter.mp h).1)]
  simp_rw [filter_erase loc (p.erase i)]

lemma rooted_remove (T : Finset V) (A : Finset V) (p : Finset I) {i : I} (hi : i∈p) (hA : loc i∈A) :
    root T A (moment (R:=R) loc idx Q μ p) =
      μ (idx i) • root T A (moment loc idx Q μ (p.erase i)) +
      ∑ j∈legs loc (p.erase i) T, Q.cov (idx i) (idx j) •
        root T (insert (loc j) A) (moment loc idx Q μ ((p.erase i).erase j)) := by
  ext s; simp only [Poly.part_plus,Poly.part_smul, Poly.part_sum, root_part]
  by_cases he : s.val ⊆ T ∧ A ⊆ s.val
  · simp only [↓reduceIte, he.1, Finset.insert_subset_iff, he.2,true_and,and_true, Finset.sum_filter]
    rw [moment_remove loc idx Q μ s p i hi (he.2 hA)]
    apply congrArg (μ (idx i)*(moment loc idx Q μ (p.erase i)).part s + ·) <| Finset.sum_congr rfl (fun j hj=> ?_)
    by_cases hw : loc j∈s.val <;> first| (simp [hw, he.1 hw]) | simp [hw]
  have hh (j : I) : ¬ (s.val ⊆ T ∧ insert (loc j) A ⊆ s.val) := fun h=>he ⟨h.1,(Finset.subset_insert _ _).trans h.2⟩
  simp_rw [if_neg he,if_neg (hh _),mul_zero,Finset.sum_const_zero,add_zero]


variable [Fintype V]
abbrev fuse (t : R.Mode) (A : Finset V) (p : Finset I) : ℂ :=
    (quotient t.val A (moment loc idx Q μ p)).part t

/-- Cost recursion, first rooted leg. At every stage the quotient has the appropriate
    denominator for the *remaining* vertices outside A. Use only for connected partitions.
    `insert` may leave `A` unchanged (Wick pairing closing a loop). -/
lemma fuse_step (t : R.Mode) (A : Finset V) (p : Finset I) {i : I} (hi : i∈p) (he : loc i ∈ A) :
    fuse loc idx Q μ t A p = μ (idx i)*fuse loc idx Q μ t A (p.erase i) +
      ∑ j∈legs loc (p.erase i) t.val, Q.cov (idx i) (idx j)*
        fuse loc idx Q μ t (insert (loc j) A) ((p.erase i).erase j) := by
  let L p : Poly R := moment loc idx Q μ p
  let T := t.val
  let q := p.erase i
  let r s := root T s (R:=R)
  let g s := quotient T s (R:=R)
  let U := inverseMass (outer T A (L p))
  -- cool numerator g: U unchanged until change_outer; every erased leg sits on fused block
  have hr (u) (hu : u∈legs loc q T) : r (insert (loc u) A) (L (q.erase u))*U = g (insert (loc u) A) (L (q.erase u)) := by
    apply change_outer (Finset.subset_insert _ _) (L p)
    intro j h h'
    have ht : loc i∉j.val := fun hj=> disjoint_left.mp h' hj (mem_insert_of_mem he)
    have hy : loc u∉j.val := fun hj=> disjoint_left.mp h' hj (mem_insert_self ..)
    exact (moment_no_see loc idx Q μ p i _ ht).trans (moment_no_see loc idx Q μ q u _ hy)
  have hg : r A (L q)*U=g A (L q) := change_outer (Finset.Subset.refl _) (L p) (L q) (fun j _ H=>
    moment_no_see loc idx Q μ p i j (fun h=> disjoint_left.mp H h he))
  change (_*U).part t=μ _* _+_
  rw [rooted_remove loc idx Q μ t.val A p hi he, add_mul, sum_mul]
  simp_rw [smul_mul_assoc, Poly.part_plus, Poly.part_sum, Poly.part_smul]
  change μ (idx i)*(r A (L q)*U).part t+_=_
  rw [hg]; refine congrArg (μ (idx i)*(g A (L q)).part t+·) ?_
  exact Finset.sum_congr rfl fun j hj=> by rw [show YM.Primitives.GCC.Anchor.root (R:=R) t.val _ _ * U = _ from hr j hj]

omit [DecidableEq I] in
lemma fuse_empty (t : R.Mode) (A : Finset V) (hA : A⊆t.val) (p : Finset I) (hp : legs loc p A = ∅) :
    fuse loc idx Q μ t A p = if A=t.val then 1 else 0 := by
  let a : R.Mode := ⟨_,R.down t.property _ hA⟩
  let m : Poly R := moment loc idx Q μ p
  have hm : m.part R.quiet=1 := by unfold m moment; rw [moments_quiet]; exact Normal.fresh ..
  have he : m.part a=1 := by rw [moment_value, show legs _ _ _=_ from hp, Normal.glyphs, prod_empty]; exact Normal.fresh ..
  change (quotient t.val a.val m).part t = _
  rw [quotient_alone t a hA m hm ?_, Poly.part_send, he]
  · split_ifs with h h' h'
    · rfl
    · exact False.elim (h' (congrArg Subtype.val h.symm))
    · exact False.elim (h (Subtype.ext h'.symm))
    rfl
  intro s hs hv
  rw [he,one_mul,moment_value,moment_value]
  suffices hr : legs loc p (diff s A).val=legs loc p s.val by rw [show a.val=A from rfl,hr]
  ext j; rw [legs,legs,mem_filter,mem_filter,show (diff s A).val = s.val\ A from rfl,mem_sdiff];
  apply and_congr_right; intro hj
  exact ⟨And.left,fun h=>⟨h,fun hz=>notMem_empty j (hp ▸ (show j∈legs loc p A from mem_filter.mpr ⟨hj,hz⟩))⟩⟩

/-- A connected-only Wick contraction algorithm. Deterministic policy may reorder the
    available rooted leg indices. 
    No additional ordering factorial. `N`
    remaining steps; always sufficient to take `p.card`.
    The distinguished root A grows along covariance edges *only*. Every charged term has
    joined ALL vertices to it (terminal equality `A=t.val`). -/
def trees (t : R.Mode) (A : Finset V) (p : Finset I) (N : ℕ) : ℂ :=
  if h : (legs loc p A).Nonempty then match N with
    | 0 => 0 -- padded, out of sufficient range
    | n+1 =>
      let i := Classical.choose h
      μ (idx i)* trees t A (p.erase i) n +
        ∑ j∈legs loc (p.erase i) t.val, Q.cov (idx i) (idx j)*
          trees t (insert (loc j) A) ((p.erase i).erase j) n
  else if A=t.val then 1 else 0
termination_by N

/-- The recursion calls use strictly fewer legs even with a loop.
    The mass quotient permits also a group fused before entering this procedure. -/
lemma tree_fuse (t : R.Mode) (A : Finset V) (hA : A⊆t.val) (p : Finset I) (N : ℕ) (he : p.card≤N) :
    trees loc idx Q μ t A p N = fuse loc idx Q μ t A p := by
  induction N generalizing p A with
  | zero =>
    have hg := card_eq_zero.mp (Nat.le_zero.mp he); subst p
    rw [trees,dif_neg,fuse_empty loc idx Q μ t A hA _ (by simp)]
    simp
  | succ n IH =>
    rw [trees]; split
    next h =>
      let i := Classical.choose h
      have hv:= mem_filter.mp (Classical.choose_spec h)
      let u := p.erase i; have hp : u.card≤n := by rw [show u.card=_ from card_erase_of_mem hv.1]; omega
      change μ (idx i)*trees loc idx Q μ t A u n+(∑ j∈legs loc u t.val, Q.cov (idx i) (idx j) * trees loc idx Q μ t (insert (loc j) A) (u.erase j) n)=_
      rw [IH A hA u hp, fuse_step loc idx Q μ t A p (i:=i) hv.1 hv.2]
      apply congrArg ( μ (idx i)*fuse loc idx Q μ t A u + · ) (Finset.sum_congr rfl (fun j hj=> ?_))
      rw [IH (insert (loc j) A) (insert_subset (mem_filter.mp hj).2 hA) (u.erase j) ((card_le_card (erase_subset ..)).trans hp)]
    next h => rw [fuse_empty loc idx Q μ t A hA p (not_nonempty_iff_eq_empty.mp h)]

lemma connected_tree (t : R.Mode) (i : V) (hi : i∈t.val) (p : Finset I) (N : ℕ) (he : p.card ≤ N) :
    (connected (moments R (Normal.blend Q μ) (word loc idx p))).part t = trees loc idx Q μ t {i} p N := by
  rw [tree_fuse loc idx Q μ t {i} (Finset.singleton_subset_iff.mpr hi) p N he, fuse,
    quotient_singleton t i _ ((moments_quiet _ _).trans (Normal.fresh ..)) hi]


omit [Fintype V] in
/-- Literal disconnection criterion for the contraction evaluation alone. Also applies with
    A singleton. Includes diagonals. May project away unnecessary loci by assigning zero
    covariances. The stronger (full connectivity) recursion above can be used for estimates;
    this test needn't classify every surviving term as nonzero. -/
theorem cut (t : R.Mode) (U A : Finset V) (hA : A⊆U) (p : Finset I) (N : ℕ) (ht : ¬ t.val⊆U)
    (hc : ∀ i∈p, loc i ∈ U → ∀ j∈p, loc j∉U → Q.cov (idx i) (idx j)=0) :
    trees loc idx Q μ t A p N=0 := by
  induction N generalizing A p with
  | zero => rw [trees]; split; rfl; exact if_neg (fun (h:A=t.val)=>ht (h ▸ hA))
  | succ n ih =>
    rw [trees]; split
    next h =>
      let i := Classical.choose h
      let q := p.erase i
      change μ (idx i)*trees loc idx Q μ t A q n + (∑ j∈legs loc q t.val, Q.cov (idx i) (idx j) * trees loc idx Q μ t (insert (loc j) A) (q.erase j) n)=0
      have hq := Finset.erase_subset i p
      have hx (l:Finset I) (hl:l⊆p) : ∀ k∈l, loc k∈U → ∀ j∈l, loc j∉ U → Q.cov (idx k) (idx j)=0 :=
        fun k hk he j hj hh=>hc k (hl hk) he j (hl hj) hh
      rw [ih A hA q (hx q hq),mul_zero, zero_add]
      have hi : i∈p ∧ loc i∈A := mem_filter.mp (Classical.choose_spec h)
      apply Finset.sum_eq_zero; intro j hj
      by_cases hz : loc j∈U
      · rw [ih _ (Finset.insert_subset hz hA) _ (hx _ ((Finset.erase_subset _ _).trans hq)),mul_zero]
      rw [hc i hi.1 (hA hi.2) j (hq (mem_filter.mp hj).1) hz,zero_mul]
    next h=> exact if_neg (fun (he:A=t.val)=>ht (he ▸ hA))

end YM.Comparison.RG02.Cumulants.Wick
