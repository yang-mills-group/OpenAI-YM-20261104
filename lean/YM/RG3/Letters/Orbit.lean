import YM.RG3.Ink.Combined
/-!
# Frame and Article symmetry for exact merger that also changes the
unmarked-to-marked-partner dictionary. 

Compare `H03.answer`, which applies to Ovens fuel instead. Need symmetry of
*quiet* change only here; changing punctuated markers while retaining rank
zero later uses the fixed-address option instead. In particular slips
alphabet can include all rooted supports (not only live ones at their input
origins!), letting zero quiet entries map there. This avoids symmetrizing
field-dependent marked coefficients or origin positions just to satisfy the
vacuum-history SymTests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Letters.Frame
open Ac Lattice RG Wilson Function MeasureTheory Finset Marker

variable {n : Side} {ι : Type*} (D : Frame n ι)
variable (e : Equiv.Perm ι) (t : Equiv.Perm (Site n))
variable (hs : ∀ i,D.read (e i)=(D.read i).image t) (hn : ∀ i,D.need (e i)=(D.need i).image t)
include hs hn

def orbit (p : D.Patch) : D.Patch :=
  ⟨e.finsetCongr p.val,by
    obtain ⟨⟨he,H⟩,⟨i,hi,ha⟩,hA⟩ := p.property
    change Spark _ (p.val.map e.toEmbedding) ∧ _ ∧ _
    let M := p.val.map e.toEmbedding
    have hX (i) (h : i∈M) : ∃ j∈p.val,e j=i := mem_map.mp h
    have hY {i} (h : i ∈ p.val) : e i ∈ M := mem_map.mpr ⟨i,h,rfl⟩
    have hI (i) : D.Hard i ↔ D.Hard (e i) := by simp [Hard,hn]
    refine ⟨⟨he.map, fun i h j h' => ?_⟩, ⟨e i,hY hi,(hI i).mp ha⟩, fun i hi j hj hi' hd he => ?_⟩
    · obtain ⟨a,hA',rfl⟩ := hX i h
      obtain ⟨b,hB',rfl⟩ := hX j h'
      refine Relation.ReflTransGen.lift (r:=bonds D.read p.val) (p:=bonds D.read M) e ?_ a b (H a hA' b hB')
      rintro c d ⟨hc,hd,x,hx,hx'⟩; refine ⟨hY hc,hY hd,t x,?_,?_⟩
      · rw [hs]; exact mem_image_of_mem _ hx
      rw [hs]; exact mem_image_of_mem _ hx'
    obtain ⟨a,hA',rfl⟩ := hX i hi
    obtain ⟨b,hB',rfl⟩ := hX j hj
    rw [hs,hs,Finset.disjoint_image t.injective]
    exact hA hA' hB' (fun h => hi' (congrArg _ h)) ((hI a).mpr hd) ((hI b).mpr he)⟩

omit hs hn in
lemma zone_back (x : ι→Support n) (he : ∀ i,x (e i)=(x i).image t) i : x (e.symm i) = (x i).image t.symm := by
  obtain ⟨i,rfl⟩ := e.surjective i
  rw [Equiv.symm_apply_apply,he,image_image]; simp

def whirl : Equiv.Perm D.Patch where
  toFun := D.orbit e t hs hn
  invFun := D.orbit e.symm t.symm (zone_back _ _ _ hs) (zone_back _ _ _ hn)
  left_inv i := Subtype.ext (show e.symm.finsetCongr (e.finsetCongr i.val) = _ from e.finsetCongr.left_inv i.val)
  right_inv i := Subtype.ext (show e.finsetCongr (e.symm.finsetCongr i.val) = _ from e.finsetCongr.right_inv i.val)

omit hs hn in
lemma zone_fwd (x : ι→Support n) (he : ∀ i,x (e i)=(x i).image t) (s : Finset ι) :
    (e.finsetCongr s).biUnion x = (s.biUnion x).image t := by
  ext1 y
  simp only [mem_biUnion,mem_image]
  constructor
  · rintro ⟨i,hi,hy⟩
    obtain ⟨a,ha,rfl⟩ := mem_map.mp (show i∈s.map _ from hi)
    change y ∈ x (e a) at hy
    rw [he] at hy
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
    exact ⟨b,⟨a,ha,hb⟩,rfl⟩
  rintro ⟨b,⟨a,ha,hb⟩,rfl⟩
  exact ⟨e a, (show e a ∈ s.map e.toEmbedding from mem_map.mpr ⟨a,ha,rfl⟩),(he a).symm ▸ mem_image_of_mem _ hb⟩

@[simp] theorem spin_ground (i : D.Patch) : D.ground (D.whirl e t hs hn i)=(D.ground i).image t :=
  zone_fwd _ _ _ hs _
@[simp] theorem spin_owns (i : D.Patch) : D.owns (D.whirl e t hs hn i)=(D.owns i).image t :=
  zone_fwd _ _ _ hn _

end YM.RG3.Letters.Frame
