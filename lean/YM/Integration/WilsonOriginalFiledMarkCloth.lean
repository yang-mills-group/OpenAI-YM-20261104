import YM.Integration.WilsonOriginalCurvedMarkCoefficient
import YM.FVAAlt2.Pipeline.Film
import YM.QuadraticLocal.Fk.Window

/-! The filed group bank and its original angular rows on its own curved thermal clock. -/
noncomputable section
namespace YM.Integration.WilsonOriginalFiledMarkCloth
open Filter Lattice Exterior Marker Multi Comparison.RG02 Comparison.RG02.Assembly
open Comparison.RG02.Adjacent Comparison.RG02.Moving.Path
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Booth RegulatorIR.FVAAlt2.Pipeline
open scoped Classical BigOperators ContDiff
variable {G:Gauge}{V:Type}[DecidableEq V]{S:Census V}{f:Side}

def row (W:Bulk.Colors S G f) (s:Hot S) (C:UnitCost) (e:ℕ) (B:fieldDir G f 1):ℂ:=
  motion (fun t=>((C.rating t)^W.power s)⁻¹ • Bulk.projected (W.mark s) (C.enter t,t • B)) (W.power s+e)

theorem original (W:Bulk.Colors S G f) (s:Hot S) (r:ℕ)
    (grade:GradeAt (W.power s) (Bulk.projected (W.mark s))) (C:UnitCost) (e:ℕ) (he:e≤r) (B:fieldDir G f 1):
    row W s C e B=born (fun i x=>(QuadraticLocal.Earn.Air.discharge W i x).part s.val) C 0 r e B:=by
  simp only [QuadraticLocal.Earn.Air.discharge,Multi.part_lit]
  simpa only [row,Complex.real_smul] using
    WilsonOriginalCurvedMarkCoefficient.original (Bulk.projected (W.mark s)) (W.power s) r grade C e he B

theorem nose (W:Bulk.Colors S G f) (u:V) (r:ℕ)
    (grade:GradeAt (W.power (Arm.pub u)) (Bulk.projected (W.mark (Arm.pub u))))
    (C:UnitCost) (e:ℕ) (he:e≤r) (B:fieldDir G f 1):
    See.noseC S u C W e B=
      born (fun i x=>(QuadraticLocal.Earn.Air.discharge W i x).part (S.fire u)) C 0 r e B:=
  original W (Arm.pub u) r grade C e he B

theorem held (W:Bulk.Colors S G f) (legal:Bulk.Well W) (u:V) (r:ℕ)
    (C:UnitCost) (e:ℕ) (he:e≤r) (B:fieldDir G f 1):
    See.noseC S u C W e B=
      born (fun i x=>(QuadraticLocal.Earn.Air.discharge W i x).part (S.fire u)) C 0 r e B:=
  nose W u r (legal.suppose_mark _) C e he B

end YM.Integration.WilsonOriginalFiledMarkCloth
end
