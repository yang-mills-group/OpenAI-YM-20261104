import YangMills.WilsonProof.TreeIndex
import YM.OPE.Nesting.Actual

set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open YangMills YangMills.Hierarchy Function Finset OPE OPE.Arboreal OPE.Nesting
open scoped Classical BigOperators

def filedLeaves (t : FusionTree) : (filedTree t).Leaf ≃ Fin t.leaves :=
  (filedLayout t).leafEquiv.trans
    { toFun := Subtype.val
      invFun := fun i => ⟨i, (rawTree t).closure (.inr i)⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }

theorem childParent (t : FusionTree) {v w : t.Vertex} (i : Fin (arity t v))
    (placed : childNode t (orderedChild t v i).1 = .inl w) : t.parent w = v := by
  have link := ((rawTree t).related _ _).1 (ordered_child_mem t v i)
  rw [placed] at link
  exact Sum.inl_injective link.2

def descendantWeight (t : FusionTree) (p : Fin t.leaves → ℝ) (v : t.Vertex) : ℝ :=
  ∑ i, if (rawTree t).Anc (.inl v) (.inr i) then p i else 0

namespace Layout
variable {t : FusionTree} {a : Node t} {T : Nesting.Tree}

theorem ratios_at (h : Layout t a T) (s : t.Vertex → ℝ) (previous : ℝ)
    (entry : ∀ v, a = .inl v → previous = s (t.parent v)) (j : T.Inner) :
    T.ratios previous (s ∘ h.vertex) j = s (h.vertex j) / s (t.parent (h.vertex j)) := by
  induction h generalizing previous with
  | leaf i => exact nomatch j
  | fork v f child ih =>
    rcases j with root | ⟨i,j⟩
    · change s v / previous = s v / s (t.parent v)
      rw [entry v rfl]
    · exact ih i (s v) (fun w hw => congrArg s (childParent t i hw).symm) j

theorem head_at (h : Layout t a T) (p : Fin t.leaves → ℝ) (j : T.Inner) :
    T.headSum (p ∘ h.leafLabel) j = descendantWeight t p (h.vertex j) := by
  induction h with
  | leaf i => exact nomatch j
  | fork v f child ih =>
    rcases j with root | ⟨i,j⟩
    · let H := Layout.fork v f child
      let P := fun i : Fin t.leaves => (rawTree t).Anc (.inl v) (.inr i)
      change (∑ i : (Nesting.Tree.fork _ f).Leaf, p (H.leafLabel i)) = ∑ i, if P i then p i else 0
      calc
        _ = ∑ i : Subtype P, p i.1 := H.leafEquiv.sum_comp (fun i => p i.1)
        _ = ∑ i ∈ univ.filter P, p i := (Finset.sum_subtype (univ.filter P) (by simp [P]) p).symm
        _ = _ := Finset.sum_filter ..
    · exact ih i j
end Layout

theorem filedRatio (t : FusionTree) (s : t.Vertex → ℝ) (j : Address t) :
    (filedTree t).ratios 1 (s ∘ (filedLayout t).vertex) (.inr j) = t.ratio s (branchIndex t j) := by
  rcases j with ⟨i,j⟩
  let layout := (layout_exists t (childNode t (orderedChild t 0 i).val)).choose_spec.some
  rw [FusionTree.ratio, branchIndex_succ]
  exact layout.ratios_at s (s 0) (fun w hw => congrArg s (childParent t i hw).symm) j

def filedCutoff (t : FusionTree) (D : Fin t.branches → ℕ) (j : (filedTree t).Inner) : ℕ :=
  Fin.cases 0 D (filedVertices t j)

theorem filedCutoff_at (t : FusionTree) (D : Fin t.branches → ℕ) (j : Address t) :
    filedCutoff t D (.inr j) = D (branchIndex t j) := by
  unfold filedCutoff
  rw [← branchIndex_succ]
  rfl

theorem filedGain (t : FusionTree) (D : Fin t.branches → ℕ) (s : t.Vertex → ℝ) :
    Nesting.Tree.nestPrice (s ∘ (filedLayout t).vertex) (filedCutoff t D) = t.cutoffGain D s := by
  unfold Nesting.Tree.nestPrice FusionTree.cutoffGain
  simp_rw [filedRatio, filedCutoff_at]
  exact (branchEquiv t).sum_comp (fun i => (t.ratio s i)^(D i + 1))

variable {g : GaugeGroup} {C : WilsonFamily g}

theorem filedToll (t : FusionTree) (H : Hierarchy C) (a : Fin t.leaves → H.Tag)
    (out ε : ℝ) (s : t.Vertex → ℝ) :
    Nesting.Tree.toll (fun i => ((a (filedLeaves t i)).1 : ℝ)) ε out (s ∘ (filedLayout t).vertex) =
      t.powerBound H out ε a s := by
  let p := fun i : Fin t.leaves => ((a i).1 : ℝ)
  have mass (v : t.Vertex) : descendantWeight t p v = t.leafWeight H a v := by
    simp only [descendantWeight, FusionTree.leafWeight, leaf_ancestor, p]
  unfold Nesting.Tree.toll FusionTree.powerBound
  rw [show (∑ i, ((a (filedLeaves t i)).1 : ℝ)) = H.weight a from (filedLeaves t).sum_comp p]
  congr 1
  calc
    _ = ∏ j : Address t, (t.ratio s (branchIndex t j))^(-t.leafWeight H a (branchIndex t j).succ - ε) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [filedRatio, branchIndex_succ]
      change _ ^ (-(filedTree t).headSum (p ∘ (filedLayout t).leafLabel) (.inr j) - ε) = _ ^ _
      rw [(filedLayout t).head_at, mass]
      rfl
    _ = _ := (branchEquiv t).prod_comp (fun i => (t.ratio s i)^(-t.leafWeight H a i.succ - ε))

end YM.Integration.WilsonSharpPhysicalTreeGeometry
