import YangMills.WilsonProof.TreeReader
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryConvoy
import YangMills.WilsonProof.NativeSupport.HierarchyBridge

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open YangMills Function Finset OPE OPE.Orbits OPE.Orbits.Reader OPE.Arboreal Spec Table
open scoped Classical BigOperators

variable {g : YangMills.GaugeGroup} {C : Family g.core} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

/-- Internal placeholder tokens are never read by a leaf-input sum. -/
def rawTokens (t : YangMills.Hierarchy.FusionTree) (a : Fin t.leaves → S.Tag) : Node t → C.book.Token :=
  Sum.elim (fun _ => ⟨0, 0⟩) (quoteTag ∘ a)

def rawTags (t : YangMills.Hierarchy.FusionTree) (a : Fin t.leaves → S.Tag) : ↥(rawTree t).leaves → S.Tag :=
  a ∘ (leafEquiv t).symm

@[simp] theorem rawTokens_grade (t : YangMills.Hierarchy.FusionTree) (a : Fin t.leaves → S.Tag) (i : Fin t.leaves) :
    (rawTokens t a (.inr i)).1 = (a i).1 := rfl

@[simp] theorem rawTags_comp (t : YangMills.Hierarchy.FusionTree) (a : Fin t.leaves → S.Tag) :
    rawTags t a ∘ leafEquiv t = a := by funext i; simp [rawTags]

@[simp] theorem rawPosition_comp (t : YangMills.Hierarchy.FusionTree) (x : Fin t.leaves → E4) (z : t.Vertex → E4) :
    crop (rawPosition t x z) (rawTree t).leaves ∘ leafEquiv t = x := rfl

theorem rawTokens_names (t : YangMills.Hierarchy.FusionTree) (a : Fin t.leaves → S.Tag) :
    crop (rawTokens t a) (rawTree t).leaves = names (fun j => (rawTags t a j).2) := by
  funext j
  obtain ⟨i, rfl⟩ := (leafEquiv t).surjective j
  change quoteTag (a i) = quoteTag (a ((leafEquiv t).symm ((leafEquiv t) i)))
  rw [Equiv.symm_apply_apply]

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]


open private grouped_eq from YangMills.WilsonProof.NativeSupport.HierarchyBridge


set_option maxHeartbeats 1000000 in
/-- One exterior tuple is kept in the original public correlation and in every through-h term. -/
theorem public_formula_permute (e : I ≃ J) (q : Viewers F) (a : J → S.Tag) (x : J → E4) (o : E4)
    (b : K → S.Tag) (y : K → E4) (h : ℕ) (hx : Injective (beside x y)) :
    (YangMills.hierarchy F Q).grouped q (a ∘ e) (x ∘ e) b y -
      (YangMills.hierarchy F Q).truncatedWithSpectators h q (a ∘ e) (x ∘ e) o b y =
        formula F Q x o (fun j => (a j).2) y (fun j => (b j).2) h q := by
  let v : Labels S (fun i => (a i).1) := fun i => (a i).2
  let w : Labels S (fun j => (b j).1) := fun j => (b j).2
  have first := whole_perm (S := S) (d := fun i => (a i).1) (e := fun j => (b j).1)
    (spectator F q) e (Equiv.refl K) (x := x) (v := v) (y := y) (w := w) (spectate F q) hx
  rw [grouped_eq, public_truncation, formula]
  apply congrArg₂ (fun u w : ℂ => u - w)
  · exact first
  · unfold trunc
    apply sum_congr rfl
    intro m _
    apply sum_congr rfl
    intro c _
    exact congrArg (fun value : ℂ => value * _) (coef_permute F Q e a x o m.val c)

set_option maxHeartbeats 1000000 in
theorem public_formula (t : YangMills.Hierarchy.FusionTree) (q : Viewers F) (a : Fin t.leaves → S.Tag)
    (x : Fin t.leaves → E4) (z : t.Vertex → E4) (b : K → S.Tag) (y : K → E4) (h : ℕ)
    (hx : Injective (beside (crop (rawPosition t x z) (rawTree t).leaves) y)) :
    (YangMills.hierarchy F Q).grouped q a x b y -
      (YangMills.hierarchy F Q).truncatedWithSpectators h q a x (z 0) b y =
        formula F Q (crop (rawPosition t x z) (rawTree t).leaves) (z 0)
          (fun j => (rawTags t a j).2) y (fun j => (b j).2) h q := by
  have answer := public_formula_permute F Q (leafEquiv t) q (rawTags t a)
    (crop (rawPosition t x z) (rawTree t).leaves) (z 0) b y h hx
  let observed (labels : Fin t.leaves → S.Tag) (positions : Fin t.leaves → E4) : ℂ :=
    (YangMills.hierarchy F Q).grouped q labels positions b y -
      (YangMills.hierarchy F Q).truncatedWithSpectators h q labels positions (z 0) b y
  have transport := congrArg₂ observed (rawTags_comp t a) (rawPosition_comp t x z)
  exact transport.symm.trans answer

end YM.Integration.WilsonSharpPhysicalTreeGeometry
