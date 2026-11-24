import YM.Nonperturbative.HeadlineSpec
import YangMills.WilsonProof.Hierarchy
import YangMills.WilsonProof.NativeSupport.HierarchyBridge
import YangMills.WilsonProof.NativeSupport.IssuedRuns.FinalWilsonData

noncomputable section
namespace IssuedBridge.FieldQuotient
open YM YangMills YangMills.Wilson
open YM.Spec YM.OPE YM.OPE.Orbits YM.Nonperturbative YM.Boundary
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

theorem adjoints {g : GaugeGroup} {C : YM.Family g.core} (h : C.Makes)
    (hg : g.IsSimple) (B : Maxwell.Reference g)
    {p : YM.Extraction.Order} {S : YM.Table C.book} (F : Final C p S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) :
    (IssuedRuns.FinalWilsonData.original C h hg B).AdjointOn (hierarchy F Q) := by
  constructor
  · rintro ⟨degree, w⟩
    obtain ⟨v, hv⟩ := S.onto degree w
    refine ⟨⟨degree, v⟩, ?_⟩
    exact congrArg (fun x : S.Field degree => (⟨degree, x⟩ : S.Tag)) hv
  · rintro ⟨degree, v⟩
    change S.pin degree (S.project degree (C.book.adj degree YM.timeAxis v)) =
      F.action.J (S.pin degree (S.project degree v))
    rw [F.realization.qt.induced, S.adj_project]
  · intro degree
    exact ⟨S.project degree, fun _ => rfl⟩
  · rfl

end IssuedBridge.FieldQuotient
end
#print axioms IssuedBridge.FieldQuotient.adjoints
