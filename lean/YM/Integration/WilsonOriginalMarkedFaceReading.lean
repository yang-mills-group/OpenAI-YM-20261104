import YM.Integration.WilsonOriginalFiledMarkCloth

/-! One already issued occupied group field as a single numerical slot. -/
noncomputable section
namespace YM.Integration.WilsonOriginalMarkedFaceReading
open Lattice Exterior Marker Multi Comparison.RG02 Comparison.RG02.Assembly Comparison.RG02.Adjacent
open RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline
open scoped Classical
variable {G:Gauge}{V:Type}[DecidableEq V]{J:Census V}{n:Side}

def field (W:Bulk.Colors J G n) (s:Hot J) (marks:Census Unit):Bulk.Colors marks G n where
  vac:=W.vac
  mark _:=W.mark s
  power _:=W.power s

theorem legal (W:Bulk.Colors J G n) (s:Hot J) (marks:Census Unit) (h:Bulk.Well W):
    Bulk.Well (field W s marks):=
  ⟨h.suppose_vac,fun _=>h.suppose_mark s,h.natural,fun _=>h.gauges s,
    h.envelope,fun _=>h.prices s⟩

theorem original (W:Bulk.Colors J G n) (s:Hot J) (marks:Census Unit) (C:UnitCost) (e:ℕ) (x:fieldDir G n 1):
    See.noseC marks () C (field W s marks) e x=WilsonOriginalFiledMarkCloth.row W s C e x:=rfl

theorem heard (W:Bulk.Colors J G n) (s:Hot J) (marks:Census Unit) (r:ℕ)
    (grade:GradeAt (W.power s) (Bulk.projected (W.mark s))) (C:UnitCost) (e:ℕ) (he:e≤r) (x:fieldDir G n 1):
    See.noseC marks () C (field W s marks) e x =
      born (fun i B=>(QuadraticLocal.Earn.Air.discharge W i B).part s.val) C 0 r e x:=
  WilsonOriginalFiledMarkCloth.original W s r grade C e he x

end YM.Integration.WilsonOriginalMarkedFaceReading
end
