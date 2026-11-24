import YM.Integration.WilsonPositionProgramGroundDriver
import YM.Integration.WilsonPositionProgramDatedRelativeSource
import YM.Comparison.RG02.Assembly.Shift

/-! The leading marked field of the original sound film in its own clock on each actual page. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramFilmGround
open Function Filter Lattice Exterior Marker Multi Comparison.RG02 Comparison.RG02.Assembly
open Comparison.RG02.Adjacent RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Booth
open RegulatorIR.FVAAlt2.Pipeline
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{V:Type}[DecidableEq V]{S:Census V}{f:Side}

theorem reading (W:Bulk.Colors S G f)(u:V)(C:UnitCost)(x:fieldDir G f 1)
    (grade:GradeAt (W.power (Arm.pub u)) (Bulk.projected (W.mark (Arm.pub u)))):
    See.noseC S u C W 0 x=(QuadraticLocal.Earn.Air.discharge W 0 x).part (S.fire u):=by
  let n:=W.power (Arm.pub u)
  let F:=Bulk.projected (W.mark (Arm.pub u))
  let p:ℝ→ℝ×fieldDir G f 1:=fun t=>(C.enter t,t • x)
  let lin:ℝ→L[ℝ]fieldDir G f 1:=(ContinuousLinearMap.id ℝ ℝ).smulRight x
  let a:ℝ→ℂ:=fun t=> ((↑((C.rating t)^n)⁻¹:ℂ)-1)
  have smooth:ContDiffAt ℝ ω p 0:=C.here.prodMk lin.contDiff.contDiffAt
  have anchor:p 0=0:=Prod.ext (C.borne) (zero_smul ℝ x)
  have deriv:=C.embark.prodMk (lin.hasFDerivAt (x:=0))
  change HasFDerivAt p _ 0 at deriv
  have leading:=WilsonThermometerPositionFilmContactHead.tangent grade smooth anchor (1:ℝ)
  rw [deriv.fderiv] at leading
  have unit : (((ContinuousLinearEquiv.refl ℝ ℝ : ℝ →L[ℝ] ℝ).prod lin) 1)=(1,x) := by simp [lin]
  rw [unit] at leading
  change jet (F ∘ p) n 1=jet F n (1,x) at leading
  have rating:C.rating 0≠0:=C.origin.trans_ne one_ne_zero
  have da:ContDiffAt ℝ ω a 0:=by
    change ContDiffAt ℝ ω (fun t=> (↑(((C.rating t)^n)⁻¹):ℂ)-1) 0
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 ((C.smooth.pow n).inv (pow_ne_zero n rating))).sub contDiffAt_const
  have head:GradeAt 1 a:=GradeAt.anchored da (by simp [a,C.origin])
  have kept:GradeAt n (F ∘ p):=grade.coarse smooth anchor
  have tail:=head.mul kept
  have void:=tail.jet_z (1:ℝ) (show n<1+n by omega)
  have cap:Arm.shineM C W u x=a*(F ∘ p)+(F ∘ p):=by
    funext t
    change ((C.rating t)^n)⁻¹ • (F (p t))=(((↑(((C.rating t)^n)⁻¹):ℂ)-1)*(F (p t))+(F (p t)))
    rw [Complex.real_smul];ring
  have pay:jet (a*(F ∘ p)+(F ∘ p)) n 1=jet (a*(F ∘ p)) n 1+jet (F ∘ p) n 1:=by
    simp [Assembly.jet,iteratedFDeriv_add_apply (tail.smooth.of_le le_top) (kept.smooth.of_le le_top),smul_add]
  change See.noseC S u C W 0 x=(QuadraticLocal.Earn.Air.discharge W 0 x).part (Arm.pub (R:=S) u).val
  rw [QuadraticLocal.Earn.Air.discharge,Multi.part_lit]
  change jet (Arm.shineM C W u x) (n+0) 1=jet F (n+0) (1,x)
  rw [Nat.add_zero,cap,pay,void,zero_add,leading]

end YM.Integration.WilsonPositionProgramFilmGround
end
