import YangMills.WilsonProof.NativeSupport.HierarchyBridge
import YangMills.WilsonProof.NativeSupport.ObservablePhases
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.OriginalPhaseWords
open YangMills YangMills.Wilson YM YM.Spec YM.OPE.Orbits
open Filter Function Set
open scoped Topology NNReal
variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

theorem distinct (w : ObservablePhases.SeparatedWord (wilsonFamily C)) : Word.distinct w.val := by
  intro i j eq
  let castIndex (k : Fin w.val.length) : Fin (w.val.map Prod.fst).length :=
    ⟨k.val, by simp⟩
  have eq' : (w.val.get i).1 = (w.val.get j).1 := eq
  have same : castIndex i = castIndex j := List.nodup_iff_injective_get.mp w.property (by
    simpa only [List.get_eq_getElem, List.getElem_map] using eq')
  exact Fin.ext (congrArg (fun t : Fin (w.val.map Prod.fst).length => t.val) same)

theorem reading (i : F.α.space.X) (w : ObservablePhases.SeparatedWord (wilsonFamily C)) :
    ObservablePhases.signature (hierarchy F Q) i w = (F.α.ensemble i).expect w.val := by
  let x : YM.Points w.val.length := WithLp.toLp 2 (fun j => (w.val.get j).1)
  let v (j : Fin w.val.length) : C.book.Token := (w.val.get j).2
  have whole : Word.realize v x = w.val := by
    change List.ofFn (fun j : Fin w.val.length => ((w.val.get j).1,(w.val.get j).2)) = w.val
    simpa only [Prod.mk.eta] using List.ofFn_get w.val
  have separated : x ∈ conf _ := (Word.realized v x).mp (by rw [whole]; exact distinct w)
  have respects : (F.α.ensemble i).respects S := by
    intro d
    rw [F.phase.phase.retains i d]
  change S.useAt (F.α.ensemble i) x (S.classTokens ∘ v) = _
  rw [Table.at_project S _ (F.phase.phase.states i).laws.toSymmetric respects separated v]
  rfl

theorem compression (i : F.α.space.X) (w : ObservablePhases.SeparatedWord (wilsonFamily C))
    (s : YM.E4) (d : ℝ≥0) (hs : YM.OS.Slab YM.timeAxis d (Word.carry w.val s)) :
    ObservablePhases.signature (hierarchy F Q) i w =
      F.α.space.character i (F.α.unselected.slot _ _ hs) :=
  (reading F Q i w).trans (F.phase.phase.chosen i w.val (distinct w) s d hs)

end IssuedBridge.OriginalPhaseWords
end
