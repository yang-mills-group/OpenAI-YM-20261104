import YangMills.WilsonProof.TreeClearance

set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open YangMills.Hierarchy Function OPE OPE.Arboreal OPE.Nesting
open scoped BigOperators Classical

namespace Layout
open private unique_child from YangMills.WilsonProof.TreeLayout
variable {t : FusionTree} {a : Node t} {T : Nesting.Tree}

theorem vertex_below (h : Layout t a T) (j : T.Inner) :
    (rawTree t).Anc a (.inl (h.vertex j)) := by
  induction h with
  | leaf i => exact nomatch j
  | fork v f child ih =>
    rcases j with root | ⟨i, j⟩
    · exact OPE.Arboreal.Anc.same _ _
    · exact (OPE.Arboreal.Anc.child (ordered_child_mem t v i)).joins (ih i j)

private theorem belowChild_ne {v : t.Vertex} {f : Fin (arity t v) → Nesting.Tree}
    (child : ∀ i, Layout t (childNode t (orderedChild t v i).1) (f i))
    (i : Fin (arity t v)) (j : (f i).Inner) : (child i).vertex j ≠ v := by
  intro eq
  have down := (child i).vertex_below j
  rw [eq] at down
  exact (not_lt_of_ge down.depth) ((rawTree t).higher (ordered_child_mem t v i))

theorem vertices_bijective (h : Layout t a T) :
    Bijective (fun j : T.Inner => (⟨h.vertex j, h.vertex_below j⟩ :
      {v : t.Vertex // (rawTree t).Anc a (.inl v)})) := by
  induction h with
  | leaf i =>
    constructor
    · intro j; exact nomatch j
    · rintro ⟨v, hv⟩
      exact False.elim (zone_inr t i (hv.inner (zone_inl t v)))
  | fork v f child ih =>
    constructor
    · rintro (root | ⟨i,j⟩) (root' | ⟨k,l⟩) eq
      · cases root; cases root'; rfl
      · exact False.elim (belowChild_ne child k l (congrArg Subtype.val eq).symm)
      · exact False.elim (belowChild_ne child i j (congrArg Subtype.val eq))
      · have equalVertex : (child i).vertex j = (child k).vertex l := congrArg Subtype.val eq
        have anc := (child i).vertex_below j
        rw [equalVertex] at anc
        have same := unique_child (rawTree t) (ordered_child_mem t v i) (ordered_child_mem t v k)
          anc ((child k).vertex_below l)
        have index : i = k := (Fintype.equivFin (t.Child v)).symm.injective
          (Subtype.ext (childNode_injective t same))
        subst k
        have inside : j = l := (ih i).1 (Subtype.ext equalVertex)
        subst l; rfl
    · rintro ⟨w, anc⟩
      by_cases atRoot : w = v
      · subst w; exact ⟨.inl (), rfl⟩
      obtain ⟨b, hkid, down⟩ := anc.first (fun eq => atRoot (Sum.inl_injective eq))
      let j := (childEquiv t v).symm ⟨b, hkid⟩
      let i := (Fintype.equivFin (t.Child v)) j
      have eq : childNode t (orderedChild t v i).1 = b := by
        change childNode t ((Fintype.equivFin (t.Child v)).symm ((Fintype.equivFin _) j)).1 = b
        rw [Equiv.symm_apply_apply]
        exact congrArg Subtype.val ((childEquiv t v).apply_symm_apply ⟨b,hkid⟩)
      obtain ⟨k, inside⟩ := (ih i).2 ⟨w, eq.symm ▸ down⟩
      have label : (child i).vertex k = w := congrArg (fun n :
        {j : t.Vertex // (rawTree t).Anc (childNode t (orderedChild t v i).1) (.inl j)} => n.1) inside
      exact ⟨.inr ⟨i,k⟩, Subtype.ext label⟩

/-- Each internal vertex of this subtree has exactly one recursive address. -/
def vertexEquiv (h : Layout t a T) : T.Inner ≃ {v : t.Vertex // (rawTree t).Anc a (.inl v)} :=
  Equiv.ofBijective _ h.vertices_bijective
end Layout

def filedVertices (t : FusionTree) : (filedTree t).Inner ≃ t.Vertex :=
  (filedLayout t).vertexEquiv.trans
    { toFun := Subtype.val
      invFun := fun v => ⟨v, (rawTree t).closure (.inl v)⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }

abbrev Address (t : FusionTree) := (i : Fin (arity t 0)) × (childForest t i).Inner

private theorem filed_nonzero (t : FusionTree) (j : Address t) : filedVertices t (.inr j) ≠ 0 := by
  intro eq
  have root : filedVertices t (.inl ()) = 0 := rfl
  exact Sum.inr_ne_inl ((filedVertices t).injective (eq.trans root.symm))

def branchIndex (t : FusionTree) (j : Address t) : Fin t.branches :=
  (filedVertices t (.inr j)).pred (filed_nonzero t j)

theorem branchIndex_succ (t : FusionTree) (j : Address t) :
    (branchIndex t j).succ = filedVertices t (.inr j) := Fin.succ_pred ..

/-- The product over proper recursive vertices uses every numbered nonroot exactly once. -/
def branchEquiv (t : FusionTree) : Address t ≃ Fin t.branches := Equiv.ofBijective (branchIndex t) (by
  constructor
  · intro i j eq
    apply Sum.inr_injective
    apply (filedVertices t).injective
    rw [← branchIndex_succ t i, ← branchIndex_succ t j, eq]
  · intro i
    obtain ⟨j, eq⟩ := (filedVertices t).surjective i.succ
    rcases j with root | j
    · cases root
      exact False.elim (Fin.succ_ne_zero i eq.symm)
    · exact ⟨j, Fin.succ_inj.mp ((branchIndex_succ t j).trans eq)⟩)

end YM.Integration.WilsonSharpPhysicalTreeGeometry
