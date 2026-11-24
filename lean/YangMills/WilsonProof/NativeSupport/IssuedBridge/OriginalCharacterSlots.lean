import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalPhaseWords
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.OriginalCharacterSlots
open YangMills YangMills.Wilson YM YM.Spec YM.OPE.Orbits
open Filter Function Set
open scoped Topology NNReal
variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

theorem address (w : C.book.Word) (hd : Word.distinct w) : (w.map Prod.fst).Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro i j eq
  let liftIndex (k : Fin (w.map Prod.fst).length) : Fin w.length := Fin.cast (by simp) k
  have equal : (w.get (liftIndex i)).1 = (w.get (liftIndex j)).1 := by
    simpa [liftIndex] using eq
  have same : liftIndex i = liftIndex j := hd equal
  exact Fin.ext (congrArg (fun t : Fin w.length => t.val) same)

theorem detected (i j : F.α.space.X)
    (h : ObservablePhases.signature (hierarchy F Q) i = ObservablePhases.signature (hierarchy F Q) j)
    (w : C.book.Word) (d : ℝ≥0) (hs : YM.OS.Slab YM.timeAxis d w) :
    F.α.space.character i (F.α.unselected.slot w d hs) =
      F.α.space.character j (F.α.unselected.slot w d hs) := by
  let selected : ObservablePhases.SeparatedWord (wilsonFamily C) := ⟨w,address w hs.2.1.1⟩
  have origin : Word.carry w 0 = w := by simp [Word.carry]
  have hs0 : YM.OS.Slab YM.timeAxis d (Word.carry w 0) := origin.symm ▸ hs
  have recorded (v : F.α.space.X) : ObservablePhases.signature (hierarchy F Q) v selected =
      F.α.space.character v (F.α.unselected.slot w d hs) := by
    exact (OriginalPhaseWords.compression F Q v selected 0 d hs0).trans (by simp [selected,origin])
  exact (recorded i).symm.trans ((congrFun h selected).trans (recorded j))

end IssuedBridge.OriginalCharacterSlots
end
