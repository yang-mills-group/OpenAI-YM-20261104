import YM.Ac.Tree

/-!
# RG_03: complete support selections in a change of representation

This file sets up a *re-expression*, not a blocking step and not a cluster/log
estimate. It can be used **pointwise** (we will use it with hard forced entries
and finite aggregated mask-correction letters). Old hard compatibility remains
on its actual sets. Slip sets must include every actual predicate/query used
in the correction (with the `UsesFinal` convention of RG). This version does
not allow hard-set shrinkage or growth: enlarge hard sets separately first, or
use a different lemma that does not impose an enlarged test among OLD labels.

`Frame` here is a skeleton only. Inventories are the exact nonempty flag
inventories for hard activities, empty for correction letters. In particular
ALL sets (`read`, including of every slip) are nonempty, even if values vanish.
A correction with empty support that does not vanish cannot charge a flag; e.g.
when moving a global constant keep its discrepancy on the tested mask support,
and move the other term to the global account or `v`.

Reuse `Ac.Parts` for the actual identification of connected components; no new
finite graph algorithm or assumptions about getting a connected shape. Works
also on winding sets. No tests of the numerical value in the skeleton, no
exclusions based just on "owners".
-/

set_option autoImplicit false
noncomputable section

namespace YM.RG3.Letters
open Lattice RG Ac Function Finset

variable (n : Side) (ι : Type*)

/-- Letters identifying a complete forced family plus attaching factors.
`OldOK` tests the old pairwise exclusion *only on hard letters*; old
internal extra tests are to be kept in the actual values. -/
structure Frame where
  read : ι → Support n
  need : ι → Support n
  nonempty i : (read i).Nonempty
  subset i : need i ⊆ read i

namespace Frame
variable {n ι} (D : Frame n ι)

def Hard (i : ι) := (D.need i).Nonempty

-- Old hard selection: disjoint on the hard supports ONLY, no such constraint
-- on any of the distinct exponential correction factors.
def OldOK (s : Finset ι) := (s : Set ι).Pairwise fun i j =>
  D.Hard i → D.Hard j → Disjoint (D.read i) (D.read j)

def footprint (s : Finset ι) := s.biUnion D.read
def inventory (s : Finset ι) := s.biUnion D.need

def Covers (F : Support n) (s : Finset ι) := D.inventory s = F

def ValidOld (F : Support n) (s : Finset ι) := D.OldOK s ∧ D.Covers F s

/-- A namespace-stable alphabet of new labels, not aligned up to equality
of products. Keeps all old letter names including the mask corrections
and packet labels even when the numerical product at that combination is
identically zero (e.g. forbidden marker products). -/
def Patch := {s : Finset ι // Spark D.read s ∧ (∃ i∈s,D.Hard i) ∧ D.OldOK s}

instance [DecidableEq ι] : DecidableEq D.Patch := by unfold Patch; infer_instance

def letters (P : D.Patch) : Finset ι := P.val

def ground (P : D.Patch) := D.footprint (D.letters P)
def owns (P : D.Patch) := D.inventory (D.letters P)

def NewOK (s : Finset D.Patch) := (s : Set D.Patch).PairwiseDisjoint D.ground
def ValidNew (F : Support n) (s : Finset D.Patch) := D.NewOK s ∧ s.biUnion D.owns = F

theorem letters_injective : Injective D.letters := by
  unfold Patch letters
  exact Subtype.val_injective

theorem entries_inside (s : Finset ι) {i} (hi : i∈s) : D.read i ⊆ D.footprint s :=
  subset_biUnion_of_mem _ hi

theorem owns_inside (i : D.Patch) : D.owns i ⊆ D.ground i := by
  intro x hx
  obtain ⟨j,hj,hx⟩ := mem_biUnion.mp hx
  exact mem_biUnion.mpr ⟨_,hj,D.subset j hx⟩

theorem owns_nonempty (i : D.Patch) : (D.owns i).Nonempty := by
  obtain ⟨j,hj,hx⟩ := i.property.2.1
  obtain ⟨x,hx⟩ := hx
  exact ⟨x,mem_biUnion.mpr ⟨j,hj,hx⟩⟩

theorem ground_nonempty (i : D.Patch) : (D.ground i).Nonempty :=
  (D.owns_nonempty i).mono (D.owns_inside i)

/-- In a covering new set, each patch can pass the exact flag-inventory
test at evaluation; hence one may stamp that indicator in the value too.
The same argument works for hard letters in the input selection. -/
theorem stamp {F : Support n} {s : Finset D.Patch} (h : D.ValidNew F s) {i : D.Patch}
    (hi : i∈s) : D.ground i ∩ F = D.owns i := by
  ext x
  rw [← h.2, mem_inter]
  constructor
  · rintro ⟨hx,hY⟩
    obtain ⟨j,hj,hj'⟩ := mem_biUnion.mp hY
    by_cases hj'' : i=j
    · rwa [hj'']
    exact (disjoint_left.mp (h.1 hi hj hj'') hx (D.owns_inside j hj')).elim
  intro hx
  exact ⟨D.owns_inside i hx, mem_biUnion.mpr ⟨i,hi,hx⟩⟩

theorem stamp_hard {F : Support n} {s : Finset ι} (h : D.ValidOld F s) {i}
    (hi : i∈s) (hh : D.Hard i) : D.read i ∩ F = D.need i := by
  ext x
  rw [← (show _ = F from h.2), mem_inter]
  constructor
  · rintro ⟨hx,hY⟩
    obtain ⟨j,hj,hj'⟩ := mem_biUnion.mp (show x ∈ s.biUnion _ from hY)
    by_cases hj'' : i=j
    · rwa [hj'']
    exact (disjoint_left.mp (h.1 hi hj hj'' hh ⟨x,hj'⟩) hx (D.subset j hj')).elim
  intro hx
  exact ⟨D.subset i hx, mem_biUnion.mpr ⟨i,hi,hx⟩⟩

section Reconstruct
variable [DecidableEq ι]

def flatten (s : Finset D.Patch) := s.biUnion D.letters

def Charged (s : Finset ι) := ∀ p ∈ Parts D.read s, ∃ i∈p,D.Hard i

-- This only needs incidence of each slip with an actual flag, not a
-- chosen old K to which to pin it and not any uniqueness of the witness flag.
theorem illuminated {F : Support n} {s : Finset ι} (h : D.Covers F s)
    (hh : ∀ i∈s, ¬ D.Hard i → ¬ Disjoint (D.read i) F) : D.Charged s := by
  intro p hp
  obtain ⟨_,hs⟩ := lives D.read s hp
  obtain ⟨i,hi⟩ := hs.1
  by_cases hd : D.Hard i
  · exact ⟨i,hi,hd⟩
  have he := (lives D.read s hp).1 hi
  obtain ⟨x,hx,hx'⟩ := not_disjoint_iff.mp (hh _ he hd)
  rw [← (show _ = F from h)] at hx'
  obtain ⟨j,hj,hX⟩ := mem_biUnion.mp hx'
  have hchain : chain D.read s i j := .single ⟨he,hj,x,hx,D.subset _ hX⟩
  have hj' : j∈p := by
    rw [← Ac.contains D.read hp i hi]
    exact (bright D.read _ _).mpr ⟨hj,hchain⟩
  exact ⟨j,hj',⟨x,hX⟩⟩

omit [DecidableEq ι] in
/-- Under valid new selection, the old individual letters are really
distinct across new labels. Uses the prohibition of empty read sets. -/
theorem letters_apart {s : Finset D.Patch} (h : D.NewOK s) :
    (s : Set D.Patch).PairwiseDisjoint D.letters := by
  intro i hi j hj hn
  apply disjoint_left.mpr
  intro l h1 h2
  obtain ⟨x,hx⟩ := D.nonempty l
  exact disjoint_left.mp (h hi hj hn)
    (D.entries_inside _ h1 hx) (D.entries_inside _ h2 hx)

theorem covers_flat (s : Finset D.Patch) : D.inventory (D.flatten s) = s.biUnion D.owns := by
  ext x
  simp [flatten, inventory, owns]
  constructor
  · rintro ⟨i,⟨A,hA,hI⟩,hh⟩; exact ⟨A,hA,i,hI,hh⟩
  rintro ⟨A,hA,i,hI,hh⟩; exact ⟨i,⟨A,hA,hI⟩,hh⟩

theorem flat_old {s : Finset D.Patch} (h : D.NewOK s) : D.OldOK (D.flatten s) := by
  intro i hi j hj hn hI hJ
  obtain ⟨A,hA,hi⟩ := mem_biUnion.mp (show i ∈ D.flatten s from hi)
  obtain ⟨B,hB,hj⟩ := mem_biUnion.mp (show j ∈ D.flatten s from hj)
  by_cases HE : A=B
  · subst B
    exact A.property.2.2 hi hj hn hI hJ
  exact Finset.disjoint_of_subset_left (D.entries_inside _ hi) (Finset.disjoint_of_subset_right (D.entries_inside _ hj) (h hA hB HE))

theorem parts_flat {s : Finset D.Patch} (h : D.NewOK s) :
    Parts D.read (D.flatten s) = s.image D.letters := by
  let t := s.image D.letters
  have he {p} (hp : p∈t) : ∃ i∈s,D.letters i=p := mem_image.mp hp
  have hh : ∀ i∈t,Spark D.read i := fun i hi => by
    obtain ⟨j,_,rfl⟩ := he hi; exact j.property.1
  have hp : (t : Set (Finset ι)).PairwiseDisjoint (fun i => i.biUnion D.read) := by
    intro i hi j hj hn
    obtain ⟨i,hI,rfl⟩ := he hi; obtain ⟨j,hJ,rfl⟩ := he hj
    exact h hI hJ (fun e => hn (congr_arg _ e))
  rw [show D.flatten s = t.biUnion id by ext i; simp [t,flatten]]
  exact separates D.read t hh hp

theorem flat_valid {F : Support n} {s : Finset D.Patch} (h : D.ValidNew F s) :
    D.ValidOld F (D.flatten s) ∧ D.Charged (D.flatten s) := by
  refine ⟨⟨D.flat_old h.1,(D.covers_flat s).trans h.2⟩,fun p hP => ?_⟩
  rw [D.parts_flat h.1] at hP
  obtain ⟨i,_,rfl⟩ := mem_image.mp hP
  exact i.property.2.1

/-- Exact inverse selection dictionary on the valid & charged subspaces. -/
def readPack (F : Support n) : {s : Finset D.Patch // D.ValidNew F s} →
    {s : Finset ι // D.ValidOld F s ∧ D.Charged s} :=
  fun s => ⟨D.flatten s.val,D.flat_valid s.property⟩

def leaf {F : Support n} (s : {s : Finset ι // D.ValidOld F s ∧ D.Charged s})
    (v : ↥(Parts D.read s.val)) : D.Patch :=
  ⟨v.val,(lives D.read s.val v.property).2,s.property.2 _ v.property,
    fun _ hi _ hj => s.property.1.1 ((lives D.read s.val v.property).1 hi) ((lives D.read s.val v.property).1 hj)⟩

def exportPack (F : Support n) (s : {s : Finset ι // D.ValidOld F s ∧ D.Charged s}) :
    Finset D.Patch := Finset.univ.image (D.leaf s)

theorem listed (F : Support n) (s : {s : Finset ι // D.ValidOld F s ∧ D.Charged s})
    (v : D.Patch) : v∈D.exportPack F s ↔ D.letters v ∈ Parts D.read s.val := by
  rw [exportPack,mem_image]; constructor
  · rintro ⟨p,_,rfl⟩; exact p.property
  exact fun h => ⟨⟨_,h⟩,mem_univ _,Subtype.ext rfl⟩

theorem unpack_listed (F : Support n) (s : {s : Finset ι // D.ValidOld F s ∧ D.Charged s}) :
    (D.exportPack F s).image D.letters = Parts D.read s.val := by
  ext x; rw [mem_image]; constructor
  · rintro ⟨p,hp,rfl⟩; exact (D.listed F s p).mp hp
  intro h
  exact ⟨D.leaf s ⟨_,h⟩,(D.listed F s _).mpr h,rfl⟩

theorem flat_export (F : Support n) (s : {s : Finset ι // D.ValidOld F s ∧ D.Charged s}) :
    D.flatten (D.exportPack F s) = s.val := by
  rw [← reconstruct D.read s.val, ← D.unpack_listed F s]
  ext i; simp [flatten]

theorem export_valid (F : Support n) (s : {s : Finset ι // D.ValidOld F s ∧ D.Charged s}) :
    D.ValidNew F (D.exportPack F s) := by
  constructor
  · intro i hi j hj hn
    have hi' := (D.listed F s i).1 hi
    have hj' := (D.listed F s j).1 hj
    exact separate D.read s.val hi' hj' (D.letters_injective.ne hn)
  rw [← D.covers_flat, D.flat_export]; exact s.property.1.2

theorem readPack_bijective (F : Support n) : Bijective (D.readPack F) := by
  refine ⟨fun i j H => ?_,fun s => ⟨⟨D.exportPack F s,D.export_valid F s⟩,Subtype.ext (D.flat_export F s)⟩⟩
  have he : Parts D.read (D.flatten i.val) = Parts D.read (D.flatten j.val) :=
    congr_arg (fun s => Parts D.read (Subtype.val s : Finset ι)) H
  rw [D.parts_flat i.property.1,D.parts_flat j.property.1] at he
  apply Subtype.ext
  exact Finset.image_injective D.letters_injective he

end Reconstruct
end Frame
end YM.RG3.Letters
