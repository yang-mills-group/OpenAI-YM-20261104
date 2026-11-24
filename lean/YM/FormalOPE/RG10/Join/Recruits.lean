import YM.FormalOPE.RG10.Join.Partners

/-! # Expand primitive cumulants over localized source/vertex partners

At fixed order and on ANY `I` of that cardinal, split each fuel vertex/payload into the actual
kernel pieces with their positions and supports, before taking its probe bounds. Need the
multilinearity in precisely the charged payload subset -- counting choices for *all* candidate
payloads can already give unusable volume factors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Joins
open MeasureTheory PowerSeries Finset Marker Extra.Trajectories FlatFeed Word Polar Function
open Primitives.GCC Primitives.GCC.Anchor
open scoped BigOperators Topology Classical
variable {Θ E : Type*} [Fintype Θ] [MeasurableSpace E] (F : FlatFeed Θ E) (W : Vertices (Θ × E))
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    {R : Census V} {S : Census I}

/-- Work in any subalgebra of eligible inputs (all elements ANY polynomial products again Pays).
This is just integrability, never estimating volume or probe dependence by compactness alone. -/
def accepts (P : Subalgebra ℂ (Θ × E → ℂ)) : Prop := ∀ f ∈ P, F.Pays f

variable (P : Subalgebra ℂ (Θ × E → ℂ)) (hP : accepts F P) (q : R.Mode)
include hP in
omit [Fintype V] in
lemma partners_account (φ : V → P) : accounted F R (fun i => (φ i).val) := fun _ => hP _ (P.prod_mem (fun i _ => (φ i).property))
omit [Fintype Θ] [MeasurableSpace E] [Fintype V] in
def enlist (φ : ↥q.val → P) : V → P := fun i => if h:i∈q.val then φ ⟨i,h⟩ else 0

def lineup (q : R.Mode) (φ : ↥q.val → P) : V → Θ × E→ℂ := fun i => (enlist P q φ i).val

def tally (φ : V → Θ × E → ℂ) := (connected (partners F R φ)).part q

lemma tally_congr {φ φ' : V → Θ × E → ℂ} (h : ∀ i∈q.val, φ i=φ' i) :
    tally F q φ=tally F q φ' := by
  have hv : UpTo q.val (partners F R φ) (partners F R φ') := fun s hs =>
    congr_arg F.mean (show guests φ s = guests φ' s from prod_congr rfl fun i hi => h i (hs hi))
  exact hv.conn q (Finset.Subset.refl _)

variable (i : ↥q.val) (g : ↥q.val → P)

omit [Fintype Θ] [MeasurableSpace E] [Fintype V] in
lemma enlisted (x : P) : lineup P q (Function.update g i x) = Function.update (lineup P q g) i.val (x.val) := by
  funext k
  by_cases he:k∈q.val
  · unfold lineup enlist; simp only [dif_pos he]
    by_cases hh : k=i.val
    · rw [show (⟨k,he⟩ : ↥q.val) = i from Subtype.ext hh, update_self]; simp [hh]
    rw [update_of_ne (show (⟨k,he⟩ : ↥q.val) ≠ i from fun hx => hh (congr_arg Subtype.val hx)), update_of_ne hh]; rw [dif_pos he]
  have h : k ≠ i.val:=fun h=>he (h.symm ▸ i.property)
  simp [lineup,enlist,update,h,he]

private def board (x : P) := partners F R (lineup P q (Function.update g i x))

omit [Fintype V] in
private lemma spectator (x y:P) : outer q.val {i.val} (board F P q i g x) =
    outer q.val {i.val} (board F P q i g y) := by
  ext s; unfold board; rw [outer_part,outer_part]; split <;> rename_i h
  · have he : i.val∉s.val := fun hi => disjoint_left.mp h.2 hi (mem_singleton_self i.val)
    rw [enlisted, enlisted]; apply congr_arg F.mean; unfold guests; rw [prod_update_of_notMem he,prod_update_of_notMem he]
  rfl

omit [Fintype V] [Fintype Θ] [MeasurableSpace E] in
private lemma guest (x : P) (s : R.Mode) (h : i.val∈s.val) :
    guests (lineup P q (Function.update g i x)) s = x.val * (∏ j∈s.val.erase i.val,lineup P q g j) := by
  unfold guests; rw [enlisted P q, Finset.prod_update_of_mem h,Finset.sdiff_singleton_eq_erase]

include hP in
omit [Fintype V] in
private lemma root_add (x y : P) : root q.val {i.val} (board F P q i g (x+y)) =
    root q.val {i.val} (board F P q i g x) + root q.val {i.val} (board F P q i g y) := by
  ext s; rw [Poly.part_plus]; simp_rw [root_part]; split_ifs with h
  · have he := singleton_subset_iff.mp h.2
    let φ (z : P) := guests (lineup P q (Function.update g i z)) s
    have hv : φ (x+y)=φ x+φ y := by unfold φ; simp_rw [guest P _ _ _ _ s he]; exact add_mul ..
    change F.mean (φ (x+y)) = F.mean (φ x)+F.mean (φ y)
    rw [hv]; exact mean_add (partners_account F P hP (enlist P q (update g i x)) s) (partners_account F P hP (enlist P q (update g i y)) s)
  simp

omit [Fintype V] in
private lemma root_scale (k : ℂ) (x : P) : root q.val {i.val} (board F P q i g (k • x)) =
    k • root q.val {i.val} (board F P q i g x) := by
  ext s; rw [Poly.part_smul]; simp_rw [root_part]; split_ifs with h
  · have he := singleton_subset_iff.mp h.2
    let φ (z : P) := guests (lineup P q (Function.update g i z)) s
    have hv : φ (k • x) = k • φ x := by unfold φ; simp_rw [guest P _ _ _ _ s he]; exact (smul_mul_assoc k x.val _)
    change F.mean (φ (k • x)) = k * F.mean (φ x); rw [hv, mean_smul]
  simp

-- Mathlib ML map_update may have typeclass decidableEq passed ANY; our functions `partners` not affected.
include hP in
/-- Cumulant as a multilinear map only in the actually contributing subset. -/
def award : MultilinearMap ℂ (fun _ : ↥q.val => P) ℂ := by
  refine MultilinearMap.mk' (fun x => tally F q (lineup P q x)) ?_ ?_
  · intro m i x y
    let R₁ := (board F P q i m)
    change (connected (R₁ (x+y))).part q = (connected (R₁ x)).part _ + (connected (R₁ y)).part _
    simp_rw [← (show ∀ z:P, (Anchor.quotient q.val {i.val} (R₁ z)).part q = (connected (R₁ z)).part q from fun z => PolyUtil.at_marker _ _ (partners_one F R _) q i.property)]
    dsimp only [R₁]
    unfold quotient; rw [root_add F P hP, spectator F P q i m (x+y) y, spectator F P q i m x y, add_mul, Poly.part_plus]
  · intro m i c x
    let R₁ := board F P q i m
    change (connected (R₁ (c • x))).part q = c * (connected (R₁ x)).part q
    simp_rw [← (show ∀ z:P, (Anchor.quotient q.val {i.val} (R₁ z)).part q = (connected (R₁ z)).part q from fun z => PolyUtil.at_marker _ _ (partners_one F R _) q i.property)]
    dsimp only [R₁]
    unfold quotient; rw [root_scale, spectator F P q i m (c • x) x, smul_mul_assoc, Poly.part_smul] -- check

include hP in
theorem award_eq (φ : V→P) : tally F q (fun i => (φ i).val)= award F P hP q (fun i=> φ i.val) := by
  apply tally_congr; intro i hi; simp [lineup,enlist,hi];
end YM.FormalOPE.RG10.Joins
