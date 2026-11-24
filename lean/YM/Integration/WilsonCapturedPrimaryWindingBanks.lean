import YM.Integration.WilsonCapturedPrimaryWindingPeg

/-! Both earned thermal banks appear on the same physical chart, with a single signed
angular subtraction at each retained grade. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWindingBanks
open Function Finset Lattice Wilson RG Marker Stationary
open RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.FVAAlt2 RegulatorIR.Diagram
open Comparison.RG02 Comparison.RG02.Adjacent Comparison.Density Comparison.Density.Mirrors
open WilsonIndependentCapturedAngularWinding WilsonIndependentCapturedFiledDirections
open WilsonEmittedFiledThermalGerm WilsonEmittedFiledMixedWindow
open private difference from YM.Integration.WilsonEmittedFiledThermalGerm
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {L : Type} [DecidableEq L] {M : Census L}
local notation "E" => Stationary.Link G n
local notation "I" => SiteSlot G n
local notation "pegBasis" => WilsonCapturedPrimaryWindingMonomial.basis

theorem mapped (i : WilsonEmittedRootedJetWage.Slot G n) :
    joint G n (WilsonEmittedRootedJetWage.peg G n i) = pegBasis i := by
  cases i with
  | none =>
    change (1,(edgeColor (G:=G) (n:=n)).symm 0) = ((1,0) : ℝ×(E))
    rw [map_zero]
  | some i =>
    change (0,(edgeColor (G:=G) (n:=n)).symm (edgeColor (WilsonOriginalLinkedAngularPage.ray G i))) =
      ((0,WilsonOriginalLinkedAngularPage.ray G i) : ℝ×(E))
    rw [ContinuousLinearEquiv.symm_apply_apply]

theorem physical (F : ℝ×(E)→ℂ) (d : ℕ) (smooth : ContDiffAt ℝ d F 0) :
    (∑ i : Fin d→WilsonEmittedRootedJetWage.Slot G n,
      ‖iteratedFDeriv ℝ d (F∘joint G n) 0 (WilsonEmittedRootedJetWage.peg G n ∘ i)‖) =
      ∑ i : Fin d→Option (I), ‖iteratedFDeriv ℝ d F 0 (pegBasis ∘ i)‖ := by
  rw [Assembly.contact_right _ (by simpa only [map_zero] using smooth),map_zero]
  apply sum_congr rfl
  intro i _
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,Function.comp_apply,mapped]
  rfl

theorem slice (V Z : Bulk.Colors M G n) (c₁ c₂ : UnitCost) (u:L)
    (left : Bulk.Well V) (right : Bulk.Well Z) (A B:Orders (I)) {p e toll:ℕ} (he : e ≤ p)
    (sameV: V.power (Booth.Arm.pub u)=toll) (sameZ : Z.power (Booth.Arm.pub u)=toll)
    (issued:Booth.Arm.Single c₁ V A u p toll) (scheduled:Booth.Arm.Single c₂ Z B u p toll) :
    let d:=e+toll
    let b:=(fun r (x:Tuple (I) r)=>((A e r x-B e r x:ℝ):ℂ))
    ∀a:E, Tensor.diagonal (Tensor.coeff (field c₁ V u-field c₂ Z u) d 0) (1,a)=
      WilsonEmittedAngularJointFare.held b (fun (y:E) i=>(y i:ℂ)) d a := by
  intro d b a
  have v:ContDiffAt ℝ d (field c₁ V u) 0 := (smooth _ _ _ left).of_le le_top
  have z:ContDiffAt ℝ d (field c₂ Z u) 0 := (smooth _ _ _ right).of_le le_top
  have issued_at := YM.Integration.WilsonEmittedFiledThermalGerm.ray c₁ V u left e a
  have schedule_at := YM.Integration.WilsonEmittedFiledThermalGerm.ray c₂ Z u right e a
  have income (c:UnitCost) (P:Bulk.Colors M G n) (T:Orders (I)) (receipt:Booth.Arm.Single c P T u p toll) :
      RegulatorIR.FVAAlt2.Pipeline.See.noseC M u c P e (Stationary.arm G n 1 a)=value (T e) d a := by
    have witnessed : RegulatorIR.FVAAlt2.Pipeline.See.noseC M u c P e (Stationary.arm G n 1 a)=
      Booth.Uniforms.cuff T toll e (Stationary.arm G n 1 a) := receipt.earned e he _
    rw [witnessed,Booth.Uniforms.cuff,Binding.flavor_lo]
    rfl
  have vgrade: V.power (Booth.Arm.pub u)+e=d := by rw [sameV]; dsimp [d]; omega
  have zgrade: Z.power (Booth.Arm.pub u)+e=d := by rw [sameZ]; dsimp [d]; omega
  rw [vgrade,income _ _ _ issued] at issued_at
  rw [zgrade,income _ _ _ scheduled] at schedule_at
  have split : Tensor.diagonal (Tensor.coeff (field c₁ V u-field c₂ Z u) d 0) (1,a) =
      Tensor.diagonal (Tensor.coeff (field c₁ V u) d 0) (1,a) -
      Tensor.diagonal (Tensor.coeff (field c₂ Z u) d 0) (1,a) := by
    simp only [Tensor.diagonal,Tensor.coeff,iteratedFDeriv_sub_apply v z,smul_sub,_root_.sub_apply]
  change Tensor.diagonal (Tensor.coeff (field c₁ V u-field c₂ Z u) d 0) (1,a)=_
  rw [split,issued_at,schedule_at]
  exact difference _ _ _ _

theorem original (V Z : Bulk.Colors M G n) (c₁ c₂ : UnitCost) (u:L)
    (left : Bulk.Well V) (right : Bulk.Well Z) (A B:Orders (I)) {p toll J:ℕ} (rangePay:J≤p+toll+1)
    (sameV: V.power (Booth.Arm.pub u)=toll) (sameZ : Z.power (Booth.Arm.pub u)=toll)
    (issued:Booth.Arm.Single c₁ V A u p toll) (scheduled:Booth.Arm.Single c₂ Z B u p toll)
    {fee:ℝ} (nonneg:0≤fee)
    (price:∀e:ℕ,e+toll<J →
      let d:=e+toll
      let b:=fun r (x:Tuple (I) r)=>((A e r x-B e r x:ℝ):ℂ)
      (d.factorial:ℝ)*WilsonEmittedAngularJointFare.mass b d ≤ fee) :
    ∀d<J, ∑ i : Fin d→WilsonEmittedRootedJetWage.Slot G n,
      ‖iteratedFDeriv ℝ d ((field c₁ V u-field c₂ Z u)∘joint G n) 0
        (WilsonEmittedRootedJetWage.peg G n ∘ i)‖ ≤ fee := by
  intro d live
  let F := field c₁ V u-field c₂ Z u
  have sv:=grading c₁ V u left
  have sz:=grading c₂ Z u right
  rw [sameV] at sv
  rw [sameZ] at sz
  have grade : Assembly.GradeAt toll F:=sv.sub sz
  rw [physical F d (grade.smooth.of_le le_top)]
  by_cases lower : d<toll
  · simpa only [grade.vanish d lower,zero_apply,norm_zero,sum_const_zero] using nonneg
  · let e:=d-toll
    have entry:e≤p:=by dsimp [e]; omega
    have eq:e+toll=d:=by dsimp [e]; omega
    have tested := slice V Z c₁ c₂ u left right A B entry sameV sameZ issued scheduled
    have paid := WilsonCapturedPrimaryWindingPeg.germ F (grade.smooth.of_le le_top) _ tested
    exact eq ▸ paid.trans (price e (eq ▸ live))

end YM.Integration.WilsonCapturedPrimaryWindingBanks
