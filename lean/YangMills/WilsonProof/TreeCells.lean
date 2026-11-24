import YangMills.WilsonProof.TreeExpansion

set_option autoImplicit false
set_option maxHeartbeats 85000
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open YangMills YangMills.Hierarchy Function OPE OPE.Orbits OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Atom Spec Table
open scoped Classical BigOperators
variable {g : GaugeGroup} {C : Family g.core} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (Q : Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
local notation "H" => YangMills.hierarchy F Q

namespace Contraction
def placedField (t : FusionTree) (a : Fin t.leaves → S.Tag) (channel : t.Vertex → Channel F Q) :
    Node t → S.Tag := Sum.elim (fun v => oneTag F Q (channel v).1 (channel v).2) a

theorem fieldOnLayout {t : FusionTree} {n : Node t} {T : Nesting.Tree} (l : Layout t n T)
    (a : Fin t.leaves → S.Tag) (channel : t.Vertex → Channel F Q) :
    rootField F Q T (a ∘ l.leafLabel) (channel ∘ l.vertex) = placedField F Q t a channel n := by
  cases l <;> rfl

variable (t : FusionTree) (a : Fin t.leaves → S.Tag) (x : Fin t.leaves → E4) (z : t.Vertex → E4)
variable {D : Fin t.branches → ℕ} (u : t.Selection (YangMills.hierarchy F Q) D) (m : ℕ) (c : Q.channels m)
theorem fieldOnChild {v : t.Vertex} (p : t.Child v) :
    placedField F Q t a (t.vertexChannel (H) (D := D) u m c) (childNode t p.1) = t.childField (H) (D := D) a u p := by
  obtain ⟨j | j, hj⟩ := p <;> rfl

def publicCell (v : t.Vertex) : ℂ :=
  let k := t.vertexChannel (H) (D := D) u m c v
  (H).coefficient (t.childField (H) (D := D) a u (v := v)) k.1 k.2 (t.positions x z) (z v)

theorem cellOnLayout {n : Node t} {T : Nesting.Tree} (l : Layout t n T) (j : T.Inner) :
    cell F Q T (rawPosition t x z ∘ l.place) (a ∘ l.leafLabel)
      (t.vertexChannel (H) (D := D) u m c ∘ l.vertex) j = publicCell F Q t a x z (D := D) u m c (l.vertex j) := by
  induction l with
  | leaf i => exact nomatch j
  | fork v trees child ih =>
    rcases j with ⟨⟩ | ⟨i,j⟩
    · let e := (Fintype.equivFin (t.Child v)).symm
      let k := t.vertexChannel (H) (D := D) u m c
      let layout := Layout.fork v trees child
      have points : skyline (rawPosition t x z ∘ layout.place) = t.positions (v := v) x z ∘ e := by
        funext i
        change rawPosition t x z ((child i).place (trees i).topSeat) = t.positions x z (orderedChild t v i)
        rw [(child i).place_top]
        exact rawPosition_child t v (orderedChild t v i) x z
      have fields : (fun i => rootField F Q (trees i) (a ∘ (child i).leafLabel) (k ∘ (child i).vertex)) =
          t.childField (H) (D := D) a u (v := v) ∘ e := by
        funext i
        exact (fieldOnLayout F Q (child i) a k).trans (fieldOnChild F Q t a (D := D) u m c (orderedChild t v i))
      change express Q (k v).1 (k v).2 (skyline (rawPosition t x z ∘ layout.place))
        (fun i => rootField F Q (trees i) (a ∘ (child i).leafLabel) (k ∘ (child i).vertex)) (z v) = _
      rw [points, fields]
      exact express_perm Q e (k v).1 (k v).2 (t.positions (v := v) x z) (t.childField (H) (D := D) a u) (z v)
    · exact ih i j

theorem filedProduct :
    product F Q (filedTree t) (filedPlot t x z) (a ∘ filedLeaves t)
      (t.vertexChannel (H) (D := D) u m c ∘ (filedLayout t).vertex) = ∏ v : t.Vertex, publicCell F Q t a x z (D := D) u m c v := by
  exact Fintype.prod_equiv (filedVertices t) _ _ (cellOnLayout F Q t a x z (D := D) u m c (filedLayout t))

end Contraction
end YM.Integration.WilsonSharpPhysicalTreeGeometry
