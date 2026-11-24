import YM.Integration.WilsonPositionProgramVacuumGerm

/-! The actual finite Wick prescription uses vacuum derivatives only through
two more angular orders than the requested coupling coefficient. This applies
to the full marked tensor and its common vacuum denominator on every forest. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramVacuumReceipt
open Function Filter Finset Lattice Wilson RG Marker Multi
open PhysicalNext PhysicalNext.Repeat Legato Push Input Org Precision Tree Exterior
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6
open Comparison.RG02 Comparison.RG02.Bulk Assembly Order WilsonStartup
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV
open QuadraticLocal QuadraticLocal.Fk Extra.Iteration
open scoped Topology ContDiff Classical BigOperators

variable {G:Gauge} {c f:Side} {S:StepData c f} {p:Clip} {P:PathData G} {O:ChartRatio G}
    {V : Type} [DecidableEq V] [Fintype V] {I:Census V}
    (K:Bulk.Kernel S p P O) (F:Forest S.ratio) (t:S.Choices)
    (X Y:Bulk.Colors I G f)

omit [Fintype V] in
theorem derivative (r j:ℕ) (hj:j≤r+2)
    (smooth:ContDiffAt ℝ ω (Bulk.geometric K F t Y) 0)
    (remainder : GradeAt (r+3) (Bulk.projected (fun g U=>X.vac g U-Y.vac g U))) :
    iteratedFDeriv ℝ j (Bulk.geometric K F t X) 0 =
      iteratedFDeriv ℝ j (Bulk.geometric K F t Y) 0 := by
  have paid := Bulk.joint_receipt S F remainder
  have change : Bulk.geometric K F t X =
      Bulk.geometric K F t Y + Bulk.posed S F (fun g U=>X.vac g U-Y.vac g U) := by
    funext z
    simp only [Bulk.geometric,Bulk.fee,Bulk.supplement,Bulk.posed,Pi.add_apply]
    ring
  rw [change,iteratedFDeriv_add_apply (smooth.of_le le_top) (paid.smooth.of_le le_top),
    paid.vanish j (by omega),add_zero]

theorem polarized (a:fieldDir G c 1) (r:ℕ) (marks:X.mark=Y.mark) (grades:X.power=Y.power)
    (slopes:∀j,j≤r+2→iteratedFDeriv ℝ j (Bulk.geometric K F t X) 0 =
      iteratedFDeriv ℝ j (Bulk.geometric K F t Y) 0)
    (b:Hot (Board I r)) :
    Assembly.generator (stage K F a) (hinge F) X.power (markFn S F X) (Bulk.geometric K F t X) r b =
    Assembly.generator (stage K F a) (hinge F) Y.power (markFn S F Y) (Bulk.geometric K F t Y) r b := by
  have fields : markFn S F X=markFn S F Y := by unfold markFn;rw [marks]
  let j := (Join.right b.val).val.card
  have count : j≤r := (Finset.card_le_univ _).trans_eq (Fintype.card_fin r)
  have raw : Assembly.naked (stage K F a) (hinge F) (Bulk.geometric K F t X) j =
      Assembly.naked (stage K F a) (hinge F) (Bulk.geometric K F t Y) j := by
    unfold Assembly.naked;rw [slopes _ (by omega)]
  simp only [Assembly.generator,fields,grades]
  split_ifs
  · rfl
  · exact congrArg (fun p:MvPolynomial (Precision.Key F G) ℂ=>(j.factorial:ℂ) • p) raw

theorem coefficients (a:fieldDir G c 1) (r:ℕ)
    (marks:X.mark=Y.mark) (grades:X.power=Y.power)
    (smooth:ContDiffAt ℝ ω (Bulk.geometric K F t Y) 0)
    (remainder : GradeAt (r+3) (Bulk.projected (fun g U=>X.vac g U-Y.vac g U))) :
    Bulk.Fk K F t X a r = Bulk.Fk K F t Y a r :=
  congrArg (Cumulants.Cloud.prescription (R:=Board I r) (K.covariance F t) (K.symm F t) 0)
    (funext (polarized K F t X Y a r marks grades (fun j hj=>derivative K F t X Y r j hj smooth remainder)))

variable (R:Run G) {i m h n:ℕ}
    (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls) (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
    (book : PlanV.Path D R.alloy Q h (i+1) m π Γ)

include book in
theorem legal (active : m ≤ i + 1) : Legal (Step.tape (h+2)) (π (i+1)) := by
  have state := book.1 (i+1) active le_rfl
  exact ⟨fun age ha=>⟨_,_,(D.shape h).pos _ age,(state age ha).pay⟩,fun age ha=>(state age ha).symm⟩

include book in
theorem original (paid:Extension.UV.Archive R.alloy.B) (active : m ≤ i + 1)
    (X : Bulk.Colors I G (R.family.side (i+1) n))
    {co:Side} {S:StepData co (R.family.side (i+1) n)} {p:Clip} {P:PathData G} {O:ChartRatio G}
    (K:Bulk.Kernel S p P O) (F:Forest S.ratio) (tag:S.Choices)
    (a:fieldDir G co 1) (r:ℕ) (hr:r≤h+2) :
    Bulk.Fk K F tag (Bare.bareUp I i n (H:=R.family.path) X) a r =
    Bulk.Fk K F tag (Fk.grant (π (i+1)) (Step.tape (h+2)) X) a r := by
  have bought := WilsonPositionProgramVacuumGerm.projected R D Q π Γ book I X paid
  have support := legal R D Q π Γ book active
  have form := Bulk.joint_receipt S F (Fk.level (f:=R.family.side (i+1) n) (π (i+1)) (Step.tape (h+2)) support)
  refine coefficients K F tag _ _ a r rfl rfl ?_ ?_
  · exact (Bulk.stone_smooth K F tag).add (((contDiffAt_fst.pow 2).mul
      (Bulk.officer_known K F).smooth).add form.smooth)
  · exact ⟨bought.1,fun j hj=>bought.2 j (by omega)⟩

end YM.Integration.WilsonPositionProgramVacuumReceipt
end
