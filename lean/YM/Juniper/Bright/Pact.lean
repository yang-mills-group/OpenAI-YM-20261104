import YM.Juniper.Bright.Shelf
/-!
 # Using a *local ONLY* bijection of entered items (incl footprints)

 Throw supplies known periods BIG→small, need one-way support injection
 only on fields in the respective TERRACE, not on winding sector & M cost.
 This prepares period enlargement local log. Inputs tested later.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Bright
open ConnectedActivityE6 Blaze Silica March Captain PhysicalNext PhysicalNext.Repeat Height
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Shoot SliceRows Control Pulse Mask Raw Matter Pond Gas Ursell Trees Reserves Greenbelt Deck Mint Shield Stained
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Extra.Iteration Animals Corona
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G: Gauge} {c f c' f' L : Side} {P:Teller G} {S: StepData c f} {T: Tube G S} {R : Rep G f}
    {S': StepData c' f'} {T': Tube G S'} {R' : Rep G f'}
      {W μ x C C' s:ℝ} {χ:Chi}{Q: ConnectedActivityE6.Target G P} {o:Target.Order G W} {I:Cash W x μ L Q o C T R} {I' :Cash W x μ L Q o C' T' R'}
      {j n k:ℕ}
open Shelf
variable (Y:Shelf I n) (U:Shelf I' n) (k)
structure Lamp (a:Site c)(g:Site c → Site c') where
    π : Head S→ Head S'
    marks : (Y.Window k a).image π= U.Window k (g a)
    sits : Set.InjOn π (Y.Window k a)
    tours : Set.InjOn g (neighbors (terrace n k+n) a)
    shows (i) : i∈ Y.Window k a → (I.supportP i).image g=I'.supportP (π i)
namespace Lamp
variable {Y U k} {a:Site c}{g:Site c → Site c'} (h:Lamp k Y U a g)
local notation "Z"=> Y.Window k a
local notation "K"=> U.Window k (g a)
local notation "π"=> h.π
lemma locs {t:Molecule S} (ht: t⊆Z): I'.unionP (t.image h.π)=(I.unionP t).image g:=by
    unfold Cash.unionP; rw [Finset.image_biUnion,Finset.biUnion_image]; exact biUnion_congr rfl (fun x hx=> (h.shows x (ht hx)).symm)
include h
lemma within_window {t:Molecule S}(ht:t⊆Z):Set.InjOn g (I.unionP t) := h.tours.mono (Finset.coe_subset.mpr (Y.patio _ _ ht))
lemma cheaper {t:Molecule S} (ht:t⊆Z): t.image h.π ⊆ K:= h.marks ▸ image_subset_image ht
lemma seating {t:Molecule S} (ht:t⊆Z) : Y.theme t k ↔ U.theme (t.image h.π) k :=by
  let f:= I.supportP; let F:= I'.supportP
  have he: Set.InjOn π t:= h.sits.mono (coe_subset.mpr ht)
  unfold Shelf.theme; rw [card_image_of_injOn he]; apply and_congr; swap
  · exact and_congr_right fun hv=> iff_of_true (ht.trans (filter_subset ..)) ((h.cheaper ht).trans (filter_subset ..))
  rw [← Meadow.sparkling _ F t he]; refine Meadow.capitates _ _ _ _ (Equiv.refl _) (fun i j=> ?_)
  have hy v (hv:v∈t) : I'.supportP (h.π v)=(f v).image g:= (h.shows v (ht hv)).symm
  change Ac.meets f _ _ ↔ ∃ u ∈ I'.supportP (h.π j.val), u∈ I'.supportP (h.π i.val)
  rw [hy _ i.2, hy _ j.2]; constructor
  · rintro ⟨z,hz,hk⟩; exact ⟨_,mem_image_of_mem _ hz,mem_image_of_mem _ hk⟩
  rintro ⟨z,hz,hk⟩; obtain ⟨z,hz',rfl⟩:=mem_image.mp hz; obtain ⟨v,hv,hq⟩:=mem_image.mp hk
  have heq:v=z:= h.within_window ht (show v∈ I.unionP t from mem_biUnion.mpr ⟨_,i.2,hv⟩) (show z∈ I.unionP t from mem_biUnion.mpr ⟨_,j.2,hz'⟩) hq
  exact ⟨z,hz',heq ▸ hv⟩
lemma back_frame (t : Molecule S')(hp:t⊆K) : ∃ u⊆ Z, Finset.image h.π u=t:=by
   refine ⟨(Z).filter (fun i=> h.π i∈ t),filter_subset ..,?_⟩
   ext i; constructor; · intro hi; obtain ⟨i,hk,rfl⟩:= mem_image.mp hi; exact (mem_filter.mp hk).2
   intro hi; have hI := hp hi; rw [← h.marks] at hI; obtain ⟨a,hA,rfl⟩:=mem_image.mp hI; exact mem_image_of_mem _ (mem_filter.mpr ⟨hA,hi⟩)
-- fibre per field label not aggregated by positions
lemma inv {t u:I.ThinP}{z w:I'.ThinP} (ht:t.val⊆ Z)(hu:u.val⊆ Z)(hz:t.val.image h.π=z.val)(hw:u.val.image h.π=w.val): t=u ↔ z=w := by
  refine ⟨fun hh=> Subtype.ext (hz.symm.trans (hh.symm ▸ hw)), fun hh=>?_⟩; apply Subtype.ext
  apply le_antisymm; swap
  · intro j hj; have hv:h.π j ∈ t.val.image h.π:= hz.symm ▸ hh.symm ▸ hw ▸ mem_image_of_mem _ (show j∈ u.val from hj); obtain ⟨k,hk,hv⟩:= mem_image.mp hv; exact (h.sits (ht hk) (hu hj) hv) ▸ hk
  intro j hj; have hv: h.π j ∈ u.val.image h.π:= hw.symm ▸ hh ▸ hz ▸ mem_image_of_mem _ (show j∈ t.val from hj); obtain ⟨k,hk,hv⟩:= mem_image.mp hv; exact (h.sits (hu hk) (ht hj) hv) ▸ hk
lemma mate {t: Tuple I.ThinP j} {u: Tuple I'.ThinP j} (ht:∀ i,(t i).val⊆ Z)(hu:∀ i,(u i).val= (t i).val.image h.π) :
    coefficient I.seam t=coefficient I'.seam u:=by
   apply Meadow.movement; intro i j; refine or_congr (h.inv (ht i) (ht j) (hu i|>.symm) (hu j|>.symm)) ?_
   have hf i:I'.smallAt (u i)=(I.smallAt (t i)).image g := by unfold Cash.smallAt; rw [hu]; exact h.locs (ht i)
   change Ac.meets I.smallAt (t j) (I.smallAt (t i)) ↔ Ac.meets I'.smallAt (u j) (I'.smallAt (u i)); unfold Ac.meets; rw [hf,hf]; constructor
   · rintro ⟨x,hx,hy⟩; exact ⟨_,mem_image_of_mem _ hx,mem_image_of_mem _ hy⟩
   rintro ⟨x,hx,hy⟩; obtain ⟨x,hxx,rfl⟩:=mem_image.mp hx; obtain ⟨p,hp,hP⟩:=mem_image.mp hy; exact ⟨x,hxx,h.tours (Y.patio _ a (ht j) hp) (Y.patio _ a (ht i) hxx) hP ▸ hp⟩
lemma ticketed {t: Tuple I.ThinP j} {u: Tuple I'.ThinP j} (ht:∀ i,(t i).val⊆ Z)(hu:∀ i,(u i).val= (t i).val.image h.π) :
    unionOf I'.smallAt u=(unionOf I.smallAt t).image g := by
    unfold unionOf; rw [Finset.biUnion_image]; apply biUnion_congr rfl; intro i _; show I'.unionP (u i).val=(I.unionP (t i).val).image g; rw [hu]; exact h.locs (ht i)
lemma inset {t: Tuple I.ThinP j} {u: Tuple I'.ThinP j} (ht:∀ i,(t i).val⊆ Z)(hu:∀ i,(u i).val= (t i).val.image h.π) :
    a∈ unionOf I.smallAt t ↔g a∈ unionOf I'.smallAt u:=by
    rw [h.ticketed ht hu]; refine ⟨fun he=>mem_image_of_mem _ he,fun hi=>?_⟩
    obtain ⟨b,hb,hx⟩:=mem_image.mp hi; refine h.tours ?_ (show a∈ neighbors (terrace n k+n) a from (neighbors_mem ..).2 (by simp)) hx ▸ hb
    obtain ⟨i,h,hv⟩:=mem_biUnion.mp hb; exact Y.patio _ _ (ht i) hv
end Lamp
end YM.Juniper.Bright
