import YM.Comparison.RG02.Sources.Naming

/-! A booked Fk keeps every lower connected coefficient on the original marked input. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalReceivedGradeRestriction
open Function Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree Marker Multi
open Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Sources Extra.Trajectories
open scoped Classical BigOperators Matrix.Norms.Frobenius

variable {V:Type} [Fintype V] [DecidableEq V] {J:Census V}

private def names (J:Census V):Names J J where
  e:=Embedding.refl V
  visible s:=by
    change s.val.image id ∈ J.choices
    rw [image_id]
    exact s.property

omit [Fintype V] in
private theorem share (s:J.Mode):(names J).share s=s:=by
  apply Subtype.ext
  change s.val.image id = s.val
  exact image_id

omit [Fintype V] in
private theorem look (s:Multi.Hot J):(names J).look s=s:=Subtype.ext (share s.val)

omit [Fintype V] in
private theorem pinned {G:Gauge}{f:Side}(W:Bulk.Colors J G f):Sources.pin (names J) W=W:=by
  cases W
  simp only [Sources.pin,Function.comp_def,look]

variable {G:Gauge}{c f:Side}{S:StepData c f}{p:Clip}{P:PathData G}{O:ChartRatio G}
    (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(t:S.Choices)(W:Bulk.Colors J G f)(A:fieldDir G c 1)

theorem original {q r:ℕ}(fits:q≤r)(j:ℕ)(hj:j≤q):
    Order.observe J r (Order.logMarked (Bulk.Fk K F t W A r)) j=
    Order.observe J q (Order.logMarked (Bulk.Fk K F t W A q)) j:=by
  let slots:Fin q ↪ Fin r:=⟨fun i=>⟨i.val,i.isLt.trans_le fits⟩,fun _ _ h=>Fin.ext (congrArg (fun a:Fin r=>a.val) h)⟩
  have unit:=Bulk.fk_unit K F t W A r
  have symmetric:=Order.sym_logMarked unit (Bulk.fk_sym K F t W A r)
  have h:=Order.trunc_observe (names J) slots symmetric hj
  rw [Sources.trunc_marked (names J) slots unit,Sources.criterion,pinned] at h
  ext s
  have visible:=congrArg (fun a:Poly J=>a.part s) h
  change (Order.observe J r (Order.logMarked (Bulk.Fk K F t W A r)) j).part ((names J).share s)=_ at visible
  rwa [share] at visible

end YM.Integration.WilsonOriginalReceivedGradeRestriction
