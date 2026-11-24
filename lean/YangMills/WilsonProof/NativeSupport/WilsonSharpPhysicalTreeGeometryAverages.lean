import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryReader
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryMargins
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeEdgeTickets

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open Function Filter Finset Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Arboreal
open OPE.Nesting OPE.Nesting.Atom YangMills.Hierarchy MeasureTheory WilsonCenteredNestedPairHaar WilsonSharpPhysicalTreeEdgeRows
open WilsonSharpPhysicalTreeEdgeTickets
open scoped Classical BigOperators Topology
attribute [local instance] measO borelO YM.Work.A15.compact_ortho

variable {g : YangMills.GaugeGroup} {C : Family g.core} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (t : FusionTree)

def allTags (a : Fin t.leaves → S.Tag) : Node t → S.Tag := Sum.elim (fun _ => ⟨0,0⟩) a

theorem allTags_grade (a : Fin t.leaves → S.Tag) (i : Fin t.leaves) :
    (names (voices (allTags t a)) (.inr i)).1 = (a i).1 := rfl

theorem direct_mean (a : Fin t.leaves → S.Tag) (m : ℕ) (c : Q.channels m)
    (x : Fin t.leaves → E4) (z : t.Vertex → E4)
    (live : orbitMargin Q.port m (crop (rawPosition t x z) (rawTree t).leaves) (z 0)) :
    (YangMills.hierarchy F Q).coefficient a m c x (z 0) =
      mean (direct F Q (rawTree t) (degrees (allTags t a)) (voices (allTags t a)) m c (rawPosition t x z)) := by
  let L := fun i : ↥(rawTree t).leaves => (tags (voices (allTags t a))) i.1
  let Y := crop (rawPosition t x z) (rawTree t).leaves
  calc
    _ = Q.coef m c Y (voices L) (z 0) := coef_permute F Q (leafEquiv t) L Y (z 0) m c
    _ = _ := WilsonCenteredNestedRootMean.original F Q m c Y (z 0) live (voices L)

theorem direct_integrable (a : Fin t.leaves → S.Tag) (m : ℕ) (c : Q.channels m)
    (X : Node t → E4) (live : orbitMargin Q.port m (crop X (rawTree t).leaves) (X (rawTree t).root)) (b : Bool) :
    Integrable (fun k => direct F Q (rawTree t) (degrees (allTags t a)) (voices (allTags t a)) m c X k b) haar :=
  integrable_raw F Q m m c (crop X (rawTree t).leaves)
    (fun i => (tags (voices (allTags t a))) i.1) (X (rawTree t).root) live b

theorem mean_norm (W : Ortho → Bool → ℂ) {B : ℝ} (pay : ∀ k b, ‖W k b‖ ≤ B)
    (integrable : ∀ b, Integrable (fun k => W k b) haar) : ‖mean W‖ ≤ B := by
  have zero : mean (fun _ _ => (0 : ℂ)) = 0 := by simp [mean]
  have bound := difference W (fun _ _ => (0 : ℂ)) (fun k b => by simpa using pay k b)
    (fun b => (integrable b).aestronglyMeasurable) (fun _ => integrable_zero _ _ _)
  simpa only [zero,sub_zero] using bound

end YM.Integration.WilsonSharpPhysicalTreeGeometry
