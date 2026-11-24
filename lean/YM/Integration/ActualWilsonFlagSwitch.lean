import YM.Integration.ActualWilsonPacketSwitch
import YM.SectorNext.VACUUM_NORMALIZATION.Covered
import YM.Planned.ATOM_FORCED_ESTIMATE.Outside

/-! The two-colour root-component exchange preserves the entire original flag admission. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonFlagSwitch
open Function Finset Lattice Wilson RG SectorNext.Vacuum ActualWilsonPacketSwitch
open scoped BigOperators Classical
variable {n : Side} {ι : Type*}

def admitted (K Z : ι → Support n) (F T : Support n) (z : Finset ι × Finset ι) : Prop :=
  accounted K Z F z.1 ∧ accounted K Z (F \ T) z.2 ∧ ∀ i ∈ z.2, Disjoint T (K i)

theorem inner_flags (K Z : ι → Support n) (hZ : ∀ i, Z i ⊆ K i) (B : Support n) (s : Finset ι)
    (H : ∀ i ∈ s, ¬Disjoint (K i) B → K i ⊆ B) :
    (inner K B s).biUnion Z = s.biUnion Z ∩ B := by
  ext x
  simp only [ActualWilsonPacketSwitch.inner,mem_inter,mem_biUnion,mem_filter]
  constructor
  · rintro ⟨i,⟨hi,ht⟩,hz⟩
    exact ⟨⟨i,hi,hz⟩,H i hi ht (hZ i hz)⟩
  · rintro ⟨⟨i,hi,hz⟩,hx⟩
    exact ⟨i,⟨hi,not_disjoint_iff.mpr ⟨x,hZ i hz,hx⟩⟩,hz⟩

theorem outer_flags (K Z : ι → Support n) (hZ : ∀ i, Z i ⊆ K i) (B : Support n) (s : Finset ι)
    (H : ∀ i ∈ s, ¬Disjoint (K i) B → K i ⊆ B) :
    (outer K B s).biUnion Z = s.biUnion Z \ B := by
  ext x
  simp only [outer,mem_sdiff,mem_biUnion,mem_filter]
  constructor
  · rintro ⟨i,⟨hi,ht⟩,hz⟩
    exact ⟨⟨i,hi,hz⟩,fun hb => Finset.disjoint_left.mp ht (hZ i hz) hb⟩
  · rintro ⟨⟨i,hi,hz⟩,hx⟩
    refine ⟨i,⟨hi,?_⟩,hz⟩
    by_contra h
    exact hx (H i hi h (hZ i hz))

theorem separate (K : ι → Support n) (B : Support n) (s t : Finset ι)
    (Hs : (s:Set ι).Pairwise fun i j => Disjoint (K i) (K j))
    (Ht : (t:Set ι).Pairwise fun i j => Disjoint (K i) (K j))
    (H : ∀ i ∈ s, ¬Disjoint (K i) B → K i ⊆ B) :
    (mix K B s t:Set ι).Pairwise fun i j => Disjoint (K i) (K j) := by
  intro i hi j hj hij
  change i ∈ inner K B s ∪ outer K B t at hi
  change j ∈ inner K B s ∪ outer K B t at hj
  rcases mem_union.mp hi with hip|hip <;> rcases mem_union.mp hj with hjp|hjp
  · exact Hs (mem_filter.mp hip).1 (mem_filter.mp hjp).1 hij
  · exact Finset.disjoint_left.mpr fun _ hi hj => Finset.disjoint_left.mp (mem_filter.mp hjp).2 hj
      (H i (mem_filter.mp hip).1 (mem_filter.mp hip).2 hi)
  · exact Finset.disjoint_left.mpr fun _ hi hj => Finset.disjoint_left.mp (mem_filter.mp hip).2 hi
      (H j (mem_filter.mp hjp).1 (mem_filter.mp hjp).2 hj)
  · exact Ht (mem_filter.mp hip).1 (mem_filter.mp hjp).1 hij

theorem moves (K Z : ι → Support n) (hZ : ∀ i, Z i ⊆ K i) (F T : Support n) (z : Finset ι × Finset ι)
    (H : admitted K Z F T z) : admitted K Z F T (exchange K T z) := by
  let B := region K T (z.1 ∪ z.2)
  have hT : T ⊆ B := root_subset K T _
  have hc (i : ι) (hi : i ∈ z.1 ∪ z.2) : ¬Disjoint (K i) B → K i ⊆ B := closed K T _ hi
  have hs i (hi : i ∈ z.1) := hc i (mem_union_left _ hi)
  have ht i (hi : i ∈ z.2) := hc i (mem_union_right _ hi)
  have hz1 : z.1.biUnion Z=F := by simpa only [Finset.ext_iff,mem_biUnion] using H.1.2
  have hz2 : z.2.biUnion Z=F \ T := by simpa only [Finset.ext_iff,mem_biUnion,mem_sdiff] using H.2.1.2
  change admitted K Z F T (mix K B z.1 z.2,mix K B z.2 z.1)
  refine ⟨⟨separate K B _ _ H.1.1 H.2.1.1 hs,?_⟩,⟨separate K B _ _ H.2.1.1 H.1.1 ht,?_⟩,?_⟩
  · have hm : (inner K B z.1 ∪ outer K B z.2).biUnion Z = F := by
      rw [Finset.union_biUnion,inner_flags K Z hZ B _ hs,outer_flags K Z hZ B _ ht,hz1,hz2]
      ext x
      simp only [mem_union,mem_inter,mem_sdiff]
      by_cases hb : x∈B
      · tauto
      have hx : x∉T := fun h => hb (hT h)
      tauto
    simpa only [Finset.ext_iff,mem_biUnion,mem_sdiff,mix] using hm
  · have hm : (inner K B z.2 ∪ outer K B z.1).biUnion Z = F \ T := by
      rw [Finset.union_biUnion,inner_flags K Z hZ B _ ht,outer_flags K Z hZ B _ hs,hz1,hz2]
      ext x
      simp only [mem_union,mem_inter,mem_sdiff]
      by_cases hb : x∈B
      · tauto
      have hx : x∉T := fun h => hb (hT h)
      tauto
    simpa only [Finset.ext_iff,mem_biUnion,mem_sdiff,mix] using hm
  · intro i hi
    rcases mem_union.mp hi with hn|hf
    · exact H.2.2 i (mem_filter.mp hn).1
    · exact Finset.disjoint_left.mpr fun _ hx hk => Finset.disjoint_left.mp (mem_filter.mp hf).2 hk (hT hx)

theorem gate (K Z : ι → Support n) (hZ : ∀ i, Z i ⊆ K i) (F T : Support n) (z : Finset ι × Finset ι) :
    admitted K Z F T (exchange K T z) ↔ admitted K Z F T z := by
  refine ⟨fun h => ?_,moves K Z hZ F T z⟩
  simpa only [involutive K T z] using moves K Z hZ F T (exchange K T z) h

def order (K : ι → Support n) (T : Support n) : (Finset ι × Finset ι) ≃ (Finset ι × Finset ι) where
  toFun := exchange K T
  invFun := exchange K T
  left_inv := involutive K T
  right_inv := involutive K T

theorem original {G : Gauge} (W : Rep G n) (T : Support n) (U : Config G n) (s t : Finset ℕ) :
    admitted (ActualWilsonPacketSplit.scopes W) (ActualWilsonPacketSplit.inventory W) (flags W.p.threshold U) T (s,t) ↔
      W.activities.admissible W.p U s ∧ Planned.Forced.ExteriorOK W.activities W.p T U t := by
  unfold admitted accounted Activities.admissible Planned.Forced.ExteriorOK Push.Local.Separate
  constructor
  · rintro ⟨⟨hs,hf⟩,⟨ht,he⟩,hd⟩
    exact ⟨⟨hs,by convert hf using 1; congr!⟩,ht,hd,by convert he using 1; congr!⟩
  · rintro ⟨⟨hs,hf⟩,ht,hd,he⟩
    exact ⟨⟨hs,by convert hf using 1; congr!⟩,⟨ht,by convert he using 1; congr!⟩,hd⟩

end YM.Integration.ActualWilsonFlagSwitch
