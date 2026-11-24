import YangMills.WilsonProof.TreeReader

set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open YangMills YangMills.Hierarchy Function MeasureTheory OPE OPE.Orbits OPE.Nesting Spec Table
open scoped Classical BigOperators

def filedPlot (t : FusionTree) (x : Fin t.leaves → E4) (z : t.Vertex → E4) : (filedTree t).Plot :=
  rawPosition t x z ∘ (filedLayout t).place

theorem filedPositions (t : FusionTree) (x : Fin t.leaves → E4) (z : t.Vertex → E4) :
    Nesting.Tree.profile (filedPlot t x z) = x ∘ filedLeaves t := by
  funext i
  change rawPosition t x z ((filedLayout t).place ((filedTree t).leafSeat i)) = _
  rw [(filedLayout t).place_leaf]
  rfl

theorem filedCenter (t : FusionTree) (x : Fin t.leaves → E4) (z : t.Vertex → E4) :
    Nesting.Tree.anchor (filedPlot t x z) = z 0 := rfl

theorem filedMeasurable (t : FusionTree) {X : Type} [MeasurableSpace X] {μ : Measure X}
    {x : X → Fin t.leaves → E4} {z : X → t.Vertex → E4} (mx : AEMeasurable x μ) (mz : AEMeasurable z μ) :
    AEMeasurable (fun k => filedPlot t (x k) (z k)) μ := by
  apply aemeasurable_pi_lambda
  intro j
  change AEMeasurable (fun k => rawPosition t (x k) (z k) ((filedLayout t).place j)) μ
  cases h : (filedLayout t).place j with
  | inl v => exact (measurable_pi_apply v).comp_aemeasurable mz
  | inr i => exact (measurable_pi_apply i).comp_aemeasurable mx

variable {g : GaugeGroup} {C : Family g.core} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (Q : Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
local notation "H" => YangMills.hierarchy F Q

theorem filedOutput (t : FusionTree) (a : Fin t.leaves → S.Tag) (x : Fin t.leaves → E4)
    (z : t.Vertex → E4) (m : ℕ) (c : Q.channels m) :
    Kernel.output F Q (filedPlot t x z) (a ∘ filedLeaves t) c = (H).coefficient a m c x (z 0) := by
  unfold Kernel.output
  rw [filedPositions, filedCenter]
  exact coef_permute F Q (filedLeaves t) a x (z 0) m c

theorem filedWhole (t : FusionTree) {J : Type} [Fintype J] (q : Viewers F)
    (a : Fin t.leaves → S.Tag) (x : Fin t.leaves → E4) (z : t.Vertex → E4)
    (b : J → S.Tag) (y : J → E4) (hx : Injective (beside x y)) :
    whole (spectator F q) (Nesting.Tree.profile (filedPlot t x z)) (voices (a ∘ filedLeaves t)) y (voices b) =
      (H).grouped q a x b y := by
  rw [filedPositions]
  exact (grouped_eq F Q q (a ∘ filedLeaves t) (x ∘ filedLeaves t) b y).symm.trans
    (grouped_permute F Q (filedLeaves t) q a x b y hx)

theorem filedTruncation (t : FusionTree) {J : Type} [Fintype J] (q : Viewers F)
    (a : Fin t.leaves → S.Tag) (x : Fin t.leaves → E4) (z : t.Vertex → E4)
    (b : J → S.Tag) (y : J → E4) (h : ℕ) :
    uponDiscount F Q h (voices (a ∘ filedLeaves t)) (voices b)
        (Kernel.cardPanel (filedPlot t x z) y) q = (H).truncatedWithSpectators h q a x (z 0) b y := by
  change trunc _ F Q h (Nesting.Tree.profile (filedPlot t x z)) (Nesting.Tree.anchor (filedPlot t x z)) _ y _ = _
  rw [filedPositions, filedCenter]
  exact (public_truncation F Q q (a ∘ filedLeaves t) (x ∘ filedLeaves t) (z 0) b y h).symm.trans
    (truncated_permute F Q (filedLeaves t) q a x (z 0) b y h)

end YM.Integration.WilsonSharpPhysicalTreeGeometry
