import YangMills.WilsonProof.TreeLayout
import YangMills.WilsonProof.TreeTests
import YM.OPE.Nesting.Quantified

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open YangMills.Hierarchy OPE OPE.Arboreal OPE.Nesting Function
open scoped Classical

private def publicNode (t : FusionTree) : Node t → t.Node := Sum.swap

private theorem location_swap (t : FusionTree) (x : Fin t.leaves → E4) (z : t.Vertex → E4)
    (j : Node t) : t.location x z (publicNode t j) = rawPosition t x z j := by
  cases j <;> rfl

private theorem below_swap (t : FusionTree) (v : t.Vertex) (j : Node t)
    (h : (rawTree t).Anc (.inl v) j) : t.below (publicNode t j) v := by
  cases j with
  | inl w =>
    obtain ⟨n, eq⟩ := h
    rw [parent_iterate] at eq
    exact ⟨n, Sum.inl_injective eq⟩
  | inr i => exact (leaf_ancestor t v i).mp h

private theorem child_swap (t : FusionTree) {v : t.Vertex} (p : t.Child v) (j : Node t)
    (h : (rawTree t).Anc (childNode t p.val) j) : t.inChild p (publicNode t j) := by
  obtain ⟨i | w, _⟩ := p
  · have eq : j = .inr i := by
      by_contra ne
      exact zone_inr t i (h.proper ne)
    subst j
    rfl
  · exact below_swap t w.succ j h

namespace Layout
variable {t : FusionTree} {a : Node t} {T : Nesting.Tree}

theorem placedBelow (h : Layout t a T) (j : T.Positions) : (rawTree t).Anc a (h.place j) := by
  induction h with
  | leaf i => exact Anc.same _ _
  | fork v f child ih =>
    cases j with
    | inl u => exact Anc.same _ _
    | inr p => exact (Anc.child (ordered_child_mem t v p.1)).joins (ih p.1 p.2)

theorem fullRelative {r M η : ℝ} {s : t.Vertex → ℝ} {x : Fin t.leaves → E4}
    {z : t.Vertex → E4} (h : Layout t a T) (clear : t.separatedAt r M η s x z) :
    Nesting.Tree.Relative M η T (s ∘ h.vertex) (rawPosition t x z ∘ h.place) := by
  induction h with
  | leaf i => trivial
  | fork v f child ih =>
    refine ⟨?_, ?_, ih⟩
    · intro j
      let h := Layout.fork v f child
      change ‖rawPosition t x z (h.place j) - z v‖ ≤ M * s v
      simpa only [location_swap] using (clear.2.2.2 v).1 (publicNode t (h.place j))
        (below_swap t v _ (h.placedBelow j))
    · intro i j k l ne
      change η * s v ≤ ‖rawPosition t x z ((child i).place k) - rawPosition t x z ((child j).place l)‖
      simpa only [location_swap] using (clear.2.2.2 v).2 (orderedChild t v i) (orderedChild t v j)
        ((Fintype.equivFin (t.Child v)).symm.injective.ne ne) _ _
        (child_swap t _ _ ((child i).placedBelow k)) (child_swap t _ _ ((child j).placedBelow l))
end Layout

abbrev childForest (t : FusionTree) (i : Fin (arity t 0)) : Nesting.Tree :=
  (layout_exists t (childNode t (orderedChild t 0 i).val)).choose

abbrev filedTree (t : FusionTree) := Nesting.Tree.fork (arity t 0) (childForest t)

def filedLayout (t : FusionTree) : Layout t (.inl 0) (filedTree t) :=
  .fork 0 (childForest t) fun i => (layout_exists t (childNode t (orderedChild t 0 i).val)).choose_spec.some

theorem atFiledTree (t : FusionTree) {r M η : ℝ} {s : t.Vertex → ℝ} {x : Fin t.leaves → E4}
    {z : t.Vertex → E4} (h : t.separatedAt r M η s x z) :
    Nesting.Accept r M η (s ∘ (filedLayout t).vertex) (rawPosition t x z ∘ (filedLayout t).place) := by
  have immediate := YangMills.WilsonProof.Tree.immediate t h
  refine ⟨(filedLayout t).tapered immediate zero_le_one r ?_, (filedLayout t).fullRelative h, h.1⟩
  intro v eq
  have hv : v = 0 := (Sum.inl_injective eq).symm
  rw [hv, h.1]

theorem atFiledExterior (t : FusionTree) {J : Type} (x : Fin t.leaves → E4) (z : t.Vertex → E4)
    (y : J → E4) (δ : ℝ) (h : t.clearOf x z y δ) :
    Nesting.Buffer (rawPosition t x z ∘ (filedLayout t).place) y δ := by
  refine ⟨fun i j => ?_, h.2⟩
  change δ ≤ ‖rawPosition t x z ((filedLayout t).place i) - y j‖
  simpa only [location_swap] using h.1 (publicNode t ((filedLayout t).place i)) j

end YM.Integration.WilsonSharpPhysicalTreeGeometry
