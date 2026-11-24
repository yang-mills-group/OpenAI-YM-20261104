import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalPhaseWords
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.OriginalUnselectedWords
open YangMills YangMills.Wilson YM YM.Spec YM.OPE.Orbits
open Filter Function Set
open scoped Topology NNReal
variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
theorem mean (w : C.book.Word) (hd : Word.distinct w) :
    ObservablePhases.read (hierarchy F Q) none w = S.expect w := by
  let x : YM.Points w.length := WithLp.toLp 2 (fun j => (w.get j).1)
  let v (j : Fin w.length) : C.book.Token := (w.get j).2
  have whole : Word.realize v x = w := by
    change List.ofFn (fun j : Fin w.length => ((w.get j).1,(w.get j).2)) = w
    simpa only [Prod.mk.eta] using List.ofFn_get w
  have separated : x ∈ conf _ := (Word.realized v x).mp (by rw [whole]; exact hd)
  change S.useAt S x (S.classTokens ∘ v) = _
  rw [Table.at_project S S F.room.kernel.laws.toSymmetric (fun _ => le_rfl) separated v]
  rfl
theorem reflectedPhase (i : F.α.space.X) (w : ObservablePhases.SeparatedWord (wilsonFamily C)) :
    (F.α.ensemble i).expect (Word.reflect w.val YM.timeAxis) =
      star (ObservablePhases.signature (hierarchy F Q) i w) := by
  rw [OriginalPhaseWords.reading F Q i w]
  exact YM.OS.twice_expect (F.phase.phase.states i).laws (F.phase.phase.states i).spin
    YM.timeAxis w.val (OriginalPhaseWords.distinct w)
end IssuedBridge.OriginalUnselectedWords
end
