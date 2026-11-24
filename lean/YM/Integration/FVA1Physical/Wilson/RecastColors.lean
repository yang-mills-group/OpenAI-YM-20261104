import YM.Integration.FVA1Physical.Wilson.SeededClockPacket

/-! One finite colored chart input for the next prescribed Wilson step.
Each finite mask is filled by the independent previous conditional log and
the same actual measured reset. The specified new vacuum is copied in full. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Lattice RG Exterior Tree Precision Marker Multi
open QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Comparison.RG02 Assembly Adjacent
open scoped Classical ContDiff
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] {R:Census I}
  {c f:Side} {S:StepData c f} {p:Clip} {P:PathData G} {O:ChartRatio G}
  (K:Bulk.Kernel S p P O) (F:Forest S.ratio) (tag:S.Choices) (C:Bulk.Colors R G f) (η:I→ℕ)
  (r:ℕ) (cost:UnitCost) (base:Bulk.Colors R G c)

def recastColors : Bulk.Colors R G c where
  vac:=base.vac
  power s:=Launch.index R η s.val+1
  mark s:=germPainter K F tag C η s r cost

theorem recast_read (valid:∀a:Hot R,C.power a=Launch.index R η a.val+1) {j:ℕ} (hj:j≤r)
    (x:fieldDir G c 1):
    Air.discharge (recastColors K F tag C η r cost base) j x=
      lit R (fun s=>loopReset K F tag C s r cost j x) :=by
  unfold Air.discharge
  apply congrArg (lit R)
  funext s
  exact germPainter_read K F tag C η s r cost valid j hj x

end YM.Integration.FVA1Physical.Wilson
