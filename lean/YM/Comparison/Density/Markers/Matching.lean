import YM.Comparison.Density.Markers.Bounds
/-!
# Reconstruct merged gas in the marker algebra

Use the existing `Pert.Attach` labels (see address flattening in that
module), not a gas compared to the first one by inequalities only. This
variation must respect exclusion for the *full marker polynomial*, even
when its vacuum part vanishes and these are genuinely new mixed terms.
The predicates and complete old support unions are unchanged, apart from
introducing the merged label. In particular no use of `NoZeroDivisors`
on marker values.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Markers
open Function Lattice RG Wilson MeasureTheory Filter Marker Finset Pert.Attach
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {V : Type} [DecidableEq V] {R : Census V} {n : Side} {G : Gauge}
variable (p : BudgetPoint) (A : Activities G n) (X : Corrections G n)

abbrev Supply (R : Census V) (G : Gauge) (n : Side) := ℕ → Config G n → Poly R
variable (K H : Supply R G n)

def bonds (U : Config G n) : Old → Poly R := Sum.elim (fun i => K i U) (fun i => H i U)

def before (U : Config G n) (s : Finset Old) :=
    if A.admissible p U s.toLeft then ∏ i∈s,bonds K H U i else 0

def chain (i : ℕ) (U : Config G n) :=
    if (page A X i).eligible p.threshold U then ∏ j∈parts A X i,bonds K H U j else 0

def packet (s : Finset ℕ) (U : Config G n) : Poly R:= if A.admissible p U s then ∏ i∈s,K i U else 0

def merged (A' : Activities G n) := packet p (Pert.Attach.attach A X p.threshold A') (chain p A X K H)

variable {K H A X p U}

private lemma well_formed {U : Config G n} (h : ∀ i,K i U≠0 → (A.forced i).eligible p.threshold U)
    {F : Activities G n} {b} (hb : (Pert.Attach.attach A X p.threshold F).admissible p U b) :
    merged (R:=R) p A X K H F b U=before p A K H U (flatten A X b) := by
  unfold merged packet before
  have hz : A.admissible p U (flatten A X b).toLeft:=
    ⟨flatten_pairwise (Or.inr trivial) hb.1,(bills_flatten _).trans hb.2⟩
  rw [if_pos hb,if_pos hz]; unfold flatten
  have he : (↑b:Set ℕ).PairwiseDisjoint (parts A X) := by
    intro i hi j hj hv
    have hi' : parts A X i ∈ Ac.Parts (X.area A) (flatten A X b) := (parts_flatten hb).symm ▸ mem_image_of_mem _ hi
    have hj' : parts A X j ∈ Ac.Parts (X.area A) (flatten A X b) := (parts_flatten hb).symm ▸ mem_image_of_mem _ hj
    exact Ac.different (X.area A) (flatten A X b) hi' hj' ((parts_inj A X).ne hv)
  rw [prod_biUnion he]; apply prod_congr rfl; intro i hi
  unfold chain; split
  · rfl
  rename_i hr
  symm
  by_contra hu
  refine hr ⟨valid_out hb hi,fun j hj=> ?_⟩
  exact (h j fun ht=> hu (prod_eq_zero (M₀:=Poly R) (mem_toLeft.mp hj) ht)).2

/-- Every occurrence carrying a nontrivial flagged adjustment can find
an old compulsory flag, even if its vacuum part vanished. -/
private lemma covers_selected {U : Config G n}
    (h : ∀ i, Healthy p.threshold (X.region i) U → H i U=0)
    (F : Activities G n) {s} (hs : before (R:=R) p A K H U s ≠ 0) :
    ∃ b, (Pert.Attach.attach A X p.threshold F).admissible p U b ∧ flatten A X b=s := by
  unfold before at hs; split at hs
  swap; · contradiction
  rename_i ha
  let L:= Ac.Parts (X.area A) s
  have he (v) (hv:v∈L) : ∃ i, parts A X i=v:= by
    obtain ⟨hi,hu⟩:=Ac.lives (X.area A) s hv
    have ht : v.toLeft.Nonempty:= by
      obtain ⟨p',hp⟩:= hu.1
      cases p' with
      | inl i=> exact ⟨i,mem_toLeft.mpr hp⟩
      | inr i=>
        have h' : ¬Healthy p.threshold (X.region i) U:= fun H=> hs (prod_eq_zero (hi hp) (h i H))
        obtain ⟨j,hj,hj'⟩:= Finset.not_disjoint_iff.mp h'
        rw [← ha.2] at hj'; obtain ⟨k,hk,hk'⟩:=mem_biUnion.mp hj'
        exact ⟨k, mem_toLeft.mpr (Ac.contains (X.area A) hv _ hp ▸ ((Ac.bright ..).2
          ⟨mem_toLeft.mp hk, .single ⟨hi hp,mem_toLeft.mp hk,j,hj,(A.forced k).inventory_sup hk'⟩⟩ : Sum.inl k ∈ _))⟩
    let X' : Pert.Attach.Cluster A X:=⟨v,hu,ht,ha.1.mono (Finset.coe_subset.mpr (toLeft_subset_toLeft hi))⟩
    exact ⟨(decoding A X).symm X',congr_arg Subtype.val ((decoding A X).apply_symm_apply X')⟩
  let b:= L.preimage (parts A X) (parts_inj A X).injOn
  have hi : b.image (parts A X) = L:= by
    ext i; constructor
    · rintro h; obtain ⟨z,hz,rfl⟩:= mem_image.mp h; exact mem_preimage.mp hz
    intro h; obtain ⟨z,rfl⟩:= he i h; exact mem_image_of_mem _ (mem_preimage.mpr h)
  have hb : flatten A X b=s:= by
    rw [show flatten A X b=(b.image (parts A X)).biUnion id by rw [image_biUnion];rfl,hi]
    exact Ac.reconstruct ..
  refine ⟨b,⟨fun i ha j hj hE=> ?_,?_⟩,hb⟩
  · exact Ac.separate (X.area A) s (mem_preimage.mp (show i∈b from ha))
      (mem_preimage.mp (show j∈b from hj)) ((parts_inj A X).ne hE)
  exact (bills_flatten _).symm.trans (by rw [hb]; exact ha.2)

/-- Use in the direction of genuinely summable values. -/
lemma full_cover {U : Config G n} {z : Poly R}
    (h : ∀ i, K i U ≠ 0 → (A.forced i).eligible p.threshold U)
    (he : ∀ i, Healthy p.threshold (X.region i) U → H i U=0) (F : Activities G n)
    (ha : HasSum (before p A K H U) z) : HasSum (fun i=>merged p A X K H F i U) z := by
  let M:= (fun i : Finset ℕ=> merged p A X K H F i U)
  let P:=before p A K H U
  have hb (i : Function.support M) : (Pert.Attach.attach A X p.threshold F).admissible p U i.val:= by
    by_contra hi; exact i.property (if_neg hi)
  have hm (i : Function.support M) : P (flatten A X i.val)= M i.val:= (well_formed h (hb i)).symm
  let j : Function.support M → Function.support P:= fun i=> ⟨flatten A X i.val, show P (flatten A X i.val) ≠ 0 from by rw [hm]; exact i.property⟩
  have hj : Injective j:= by
    intro i i' hx; refine Subtype.ext (Finset.image_injective (parts_inj A X) ?_); rw [← parts_flatten (hb i), ← parts_flatten (hb i'),show flatten A X _= _ from congrArg Subtype.val hx]
  have hk : Surjective j:= by
    intro t; obtain ⟨b,hb,hq⟩:= covers_selected he F (show before p A K H U t.val≠0 from t.property)
    exact ⟨⟨b,show M b ≠ 0 from by rw [show M b=_ from well_formed h hb,hq]; exact t.property⟩,Subtype.ext hq⟩
  exact (Equiv.ofBijective j ⟨hj,hk⟩).hasSum_iff_of_support hm|>.2 ha
end YM.Comparison.Density.Markers
