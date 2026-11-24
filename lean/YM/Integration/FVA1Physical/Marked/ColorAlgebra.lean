import YM.Integration.FVA1Physical.Marked.ColorLocality

/-! Complex polarization is multiplicative on the actual slot-local marker
families. The disjoint marker product sums exactly once over every colored
subset of the output support. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Marker Finset
open scoped BigOperators Classical
variable {I : Type} [DecidableEq I] {B : Census I}

private theorem split_colors (x y : Finset I) (sep : Disjoint x y) (f g : Finset I→ℂ)
    (hf : ∀ t t', (∀ j∈x, j∈t ↔ j∈t') → f t=f t')
    (hg : ∀ t t', (∀ j∈y, j∈t ↔ j∈t') → g t=g t') :
    (∑ t∈(x∪y).powerset,Complex.I^t.card*(f t*g t)) =
      (∑ t∈x.powerset,Complex.I^t.card*f t)*(∑ t∈y.powerset,Complex.I^t.card*g t) := by
  rw [sum_mul_sum,←sum_product']
  refine sum_bij' (fun t _=>(t∩x,t∩y)) (fun p _=>p.1∪p.2) ?_ ?_ ?_ ?_ ?_
  · intro t _
    exact mem_product.mpr ⟨mem_powerset.mpr inter_subset_right,mem_powerset.mpr inter_subset_right⟩
  · intro p hp
    obtain ⟨a,b⟩ := mem_product.mp hp
    exact mem_powerset.mpr (union_subset_union (mem_powerset.mp a) (mem_powerset.mp b))
  · intro t ht
    ext j
    have inc := mem_powerset.mp ht
    simp only [mem_union,mem_inter]
    exact ⟨fun h=>h.elim And.left And.left,fun jt=>(mem_union.mp (inc jt)).elim (fun jx=>Or.inl ⟨jt,jx⟩) (fun jy=>Or.inr ⟨jt,jy⟩)⟩
  · rintro ⟨a,b⟩ hp
    obtain ⟨ha,hb⟩ := mem_product.mp hp
    have ax := mem_powerset.mp ha
    have by' := mem_powerset.mp hb
    apply Prod.ext
    · ext j
      simp only [mem_union,mem_inter]
      exact ⟨fun h=>h.1.elim id (fun jb=>False.elim (disjoint_left.mp sep h.2 (by' jb))),fun ja=>⟨Or.inl ja,ax ja⟩⟩
    ext j
    simp only [mem_union,mem_inter]
    exact ⟨fun h=>h.1.elim (fun ja=>False.elim (disjoint_left.mp sep (ax ja) h.2)) id,fun jb=>⟨Or.inr jb,by' jb⟩⟩
  intro t ht
  have inc := mem_powerset.mp ht
  have union : (t∩x)∪(t∩y)=t := by
    ext j; simp only [mem_union,mem_inter]
    exact ⟨fun h=>h.elim And.left And.left,fun jt=>(mem_union.mp (inc jt)).elim (fun jx=>Or.inl ⟨jt,jx⟩) (fun jy=>Or.inr ⟨jt,jy⟩)⟩
  have hcard : t.card=(t∩x).card+(t∩y).card := (congrArg Finset.card union.symm).trans
    (card_union_of_disjoint (sep.mono inter_subset_right inter_subset_right))
  have left := hf t (t∩x) (fun j hj=>by simp [hj])
  have right := hg t (t∩y) (fun j hj=>by simp [hj])
  dsimp only
  rw [hcard,pow_add,left,right]
  ring

theorem SlotLocal.mul {A C : Finset I→Poly B} (ha : SlotLocal A) (hc : SlotLocal C) : SlotLocal (A*C) := by
  intro s t t' ids
  simp only [Pi.mul_apply,Poly.part_mul]
  refine sum_congr rfl fun x _=>sum_congr rfl fun y _=>?_
  split_ifs with h
  · have hx : x.val ⊆ s.val := h.2 ▸ subset_union_left
    have hy : y.val ⊆ s.val := h.2 ▸ subset_union_right
    rw [ha x t t' (fun j hj=>ids j (hx hj)),hc y t t' (fun j hj=>ids j (hy hj))]
  rfl

theorem color_product {A C : Finset I→Poly B} (ha : SlotLocal A) (hc : SlotLocal C) :
    complexWallet (A*C)=complexWallet A * complexWallet C := by
  apply Marker.Poly.ext
  intro s
  change (∑ t∈s.val.powerset,Complex.I^t.card*(A t*C t).part s) = _
  simp only [Poly.part_mul,Finset.mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _=>?_
  rw [sum_comm]
  refine sum_congr rfl fun y _=>?_
  by_cases h : Poly.merges x y s
  · simp only [if_pos h]
    change (∑ t∈s.val.powerset,_)=(∑ t∈x.val.powerset,_)*(∑ t∈y.val.powerset,_)
    rw [←h.2]
    exact split_colors x.val y.val h.1 _ _ (ha x) (hc y)
  simp [h]

end YM.Integration.FVA1Physical.Marked
