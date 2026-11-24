import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalTrainGeometry
import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalUnselectedWords
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.OriginalAdjointTrain
open YangMills YangMills.Wilson YM YM.Spec YM.OPE.Orbits
open Filter Function Set
open scoped Topology NNReal
variable {g : GaugeGroup} {C : Family g.core} {B : YangMills.Maxwell.Reference g}
variable (D : WilsonData B (wilsonFamily C))
theorem reflected (originalStar : D.starToken = C.book.reflectedToken YM.timeAxis) (w : C.book.Word) :
    ObservablePhases.reflected D w = Word.reflect w YM.timeAxis := by
  rw [Word.reflectedPoint]
  apply List.map_congr_left
  intro t _
  apply Prod.ext
  · apply PiLp.ext
    intro a
    exact (Signed.mirrored YM.timeAxis a t.1).symm
  · exact congrFun originalStar t.2

def signed (w : ObservablePhases.SeparatedWord (wilsonFamily C)) (b : Bool) : YM.Row.Core C.book :=
  if b then ⟨Word.reflect w.val YM.timeAxis, Word.reflects _ (OriginalPhaseWords.distinct w)⟩
  else ⟨w.val, OriginalPhaseWords.distinct w⟩

theorem train (originalStar : D.starToken = C.book.reflectedToken YM.timeAxis) {k : ℕ}
    (w : Fin k → ObservablePhases.SeparatedWord (wilsonFamily C)) (adjoint : Fin k → Bool) (n : ℕ) :
    ObservablePhases.train D w adjoint n =
      YM.OS.Ground.all (OriginalTrainGeometry.cars fun j => signed (w j) (adjoint j)) n := by
  simp only [ObservablePhases.train, YM.OS.Ground.all, OriginalTrainGeometry.cars, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  change ((if adjoint j then ObservablePhases.reflected D (w j).val else (w j).val).map
      (fun t => (t.1 + OriginalTrainGeometry.shift j.val n, t.2))) =
    Word.carry (signed (w j) (adjoint j)).val (OriginalTrainGeometry.shift j.val n)
  rw [reflected D originalStar]
  cases adjoint j <;> rfl

theorem readSigned {p : Extraction.Order} {S : Table C.book} (F : Final C p S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (χ : F.α.space.X) (w : ObservablePhases.SeparatedWord (wilsonFamily C)) (b : Bool) :
    (F.α.ensemble χ).expect (signed w b).val =
      if b then star (ObservablePhases.signature (hierarchy F Q) χ w)
      else ObservablePhases.signature (hierarchy F Q) χ w := by
  cases b
  · exact (OriginalPhaseWords.reading F Q χ w).symm
  · exact OriginalUnselectedWords.reflectedPhase F Q χ w
end IssuedBridge.OriginalAdjointTrain
end
