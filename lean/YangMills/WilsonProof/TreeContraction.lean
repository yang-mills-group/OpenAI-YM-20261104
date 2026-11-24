import YangMills.WilsonProof.TreeCells

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry.Contraction
open YangMills YangMills.Hierarchy Function OPE OPE.Orbits OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Composite Spec Table
open scoped Classical BigOperators
variable {g : GaugeGroup} {C : Family g.core} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (Q : Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
local notation "H" => YangMills.hierarchy F Q

def selectionEquiv (t : FusionTree) (D : Fin t.branches → ℕ) :
    t.Selection (H) D ≃ Picks F Q (filedTree t) (filedCutoff t D) :=
  (Equiv.piCongrLeft (fun i : Fin t.branches => Menu.Cut Q (D i)) (branchEquiv t)).symm.trans
    (Equiv.piCongrRight fun j : Address t =>
      Equiv.cast (congrArg (Menu.Cut Q) (filedCutoff_at t D j).symm))

theorem uncap_cast {m n : ℕ} (h : m = n) (u : Menu.Cut Q m) :
    uncap F Q (Equiv.cast (congrArg (Menu.Cut Q) h) u) = uncap F Q u := by
  subst n
  rfl

theorem filedSelection (t : FusionTree) (D : Fin t.branches → ℕ) (m : ℕ) (c : Q.channels m)
    (u : t.Selection (H) D) :
    select F Q (filedTree t) (filedCutoff t D) m ⟨Fin.last m,c⟩ (selectionEquiv F Q t D u) =
      t.vertexChannel (H) (D := D) u m c ∘ (filedLayout t).vertex := by
  funext j
  rcases j with ⟨⟩ | j
  · rfl
  · change uncap F Q (Equiv.cast (congrArg (Menu.Cut Q) (filedCutoff_at t D j).symm) (u (branchIndex t j))) =
      t.vertexChannel (H) (D := D) u m c (filedVertices t (.inr j))
    rw [← branchIndex_succ t j]
    exact uncap_cast F Q (filedCutoff_at t D j).symm (u (branchIndex t j))

/-- The recursive reader and the numbered public tree have the same finite contraction. -/
theorem filedChord (t : FusionTree) (a : Fin t.leaves → S.Tag) (x : Fin t.leaves → E4)
    (z : t.Vertex → E4) (D : Fin t.branches → ℕ) (m : ℕ) (c : Q.channels m) :
    Kernel.chord F Q (filedPlot t x z) (a ∘ filedLeaves t) c (filedCutoff t D) =
      t.iterated (H) a x z D m c := by
  rw [chordSum]
  unfold FusionTree.iterated
  symm
  apply Fintype.sum_equiv (selectionEquiv F Q t D) _ _
  intro u
  rw [filedSelection]
  exact (filedProduct F Q t a x z (D := D) u m c).symm

end YM.Integration.WilsonSharpPhysicalTreeGeometry.Contraction
