import YM.Integration.WilsonEmittedFiledThermalGerm
import YM.Integration.WilsonEmittedWindingField
import YM.Integration.WilsonEmittedRootedJetWage

/-! The original filed source has a genuine gap below its mark power.
The paid field tensors above that power control the mixed derivatives
on the actual group coordinate chart without a period-size charge. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonEmittedFiledMixedWindow
open Function Finset Lattice Wilson RG Marker QuadraticLocal RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.FVAAlt2 RegulatorIR.Diagram Comparison.RG02 Comparison.RG02.Adjacent
open Comparison.Density Comparison.Density.Mirrors Stationary WilsonIndependentCapturedAngularWinding
open WilsonEmittedFiledThermalGerm
open private billed from YM.Integration.WilsonEmittedRootedJetWage
open scoped Topology Classical ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {L : Type} [DecidableEq L] {M : Census L}
local notation "E" => Stationary.Link G n
local notation "I" => SiteSlot G n

theorem grading (c : UnitCost) (V : Bulk.Colors M G n) (u:L) (w:Bulk.Well V):
    Assembly.GradeAt (V.power (Booth.Arm.pub u)) (field c V u) := by
  let change := fun z:ℝ×(E)=>(c.enter z.1,Stationary.arm G n 1 z.2)
  have at0 : change 0=0 := by simp [change]
  have ready : ContDiffAt ℝ ω change 0 :=
    (c.here.comp 0 contDiffAt_fst).prodMk ((Stationary.arm G n 1).contDiff.contDiffAt.comp 0 contDiffAt_snd)
  have out := (w.suppose_mark (Booth.Arm.pub u)).coarse ready at0
  let wage := fun z:ℝ×(E)=>((c.rating z.1)^(V.power (Booth.Arm.pub u)))⁻¹
  have dial : ContDiffAt ℝ ω (fun z:ℝ×(E)=>c.rating z.1) 0 := c.smooth.comp 0 contDiffAt_fst
  have regularW : ContDiffAt ℝ ω wage 0 := (dial.pow _).inv (by simp [c.origin])
  have total := Assembly.GradeAt.combo (ContinuousLinearMap.lsmul ℝ ℝ : ℝ→L[ℝ]ℂ→L[ℝ]ℂ)
    (Assembly.GradeAt.unchecked regularW) out
  rw [Nat.zero_add] at total
  convert total using 1
  funext x
  rfl

def joint (G:Gauge) (n:Side) : ℝ×Directions G n →L[ℝ] ℝ×Stationary.Link G n :=
  (ContinuousLinearMap.fst ℝ ℝ (Directions G n)).prod
    ((edgeColor (G:=G) (n:=n)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ ℝ (Directions G n)))

theorem angularBound (y:Directions G n) (i:I) : ‖((edgeColor (G:=G) (n:=n)).symm y i:ℂ)‖≤‖y‖ := by
  have h := billed ((0,y):ℝ×Directions G n) (some i)
  simpa only [Complex.norm_real,WilsonEmittedRootedJetWage.weight,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)] using h

theorem pull (F:ℝ×(E)→ℂ) (d:ℕ) (smooth:ContDiffAt ℝ d F 0) :
    ‖iteratedFDeriv ℝ d (F∘joint G n) 0‖≤‖iteratedFDeriv ℝ d F 0‖ := by
  have size : ‖joint G n‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    rw [one_mul]
    change max ‖z.1‖ ‖(edgeColor (G:=G) (n:=n)).symm z.2‖ ≤ max ‖z.1‖ ‖z.2‖
    apply max_le_max le_rfl
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro q
    simpa only [Complex.norm_real] using angularBound z.2 q
  rw [Assembly.contact_right _ (by simpa only [map_zero] using smooth),map_zero]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  calc
    _ ≤ ‖iteratedFDeriv ℝ d F 0‖ * ∏ _j:Fin d,(1:ℝ) :=
      mul_le_mul_of_nonneg_left (prod_le_prod (fun _ _=>norm_nonneg _) (fun _ _=>size)) (norm_nonneg _)
    _ = _ := by simp

theorem original (V Z : Bulk.Colors M G n) (c₁ c₂ : UnitCost) (u:L)
    (left : Bulk.Well V) (right : Bulk.Well Z) (A B:Orders (I)) {p toll J:ℕ} (rangePay:J≤p+toll+1)
    (sameV: V.power (Booth.Arm.pub u)=toll) (sameZ : Z.power (Booth.Arm.pub u)=toll)
    (issued:Booth.Arm.Single c₁ V A u p toll) (scheduled:Booth.Arm.Single c₂ Z B u p toll)
    {fee:ℝ} (nonneg:0≤fee)
    (price:∀e:ℕ,e+toll<J →
      let d:=e+toll
      let b:=fun r (x:Tuple (I) r)=>((A e r x-B e r x:ℝ):ℂ)
      (d.factorial:ℝ)*Planned.AtomRegular.polarCost d*(WilsonEmittedAngularJointFare.mass b d*2^d) ≤ fee) :
    ∀ d<J, ‖iteratedFDeriv ℝ d ((field c₁ V u-field c₂ Z u)∘joint G n) 0‖ ≤ fee := by
  intro d live
  let F:=field c₁ V u-field c₂ Z u
  have sv:=grading c₁ V u left
  have sz:=grading c₂ Z u right
  rw [sameV] at sv
  rw [sameZ] at sz
  have grade : Assembly.GradeAt toll F:=sv.sub sz
  apply (pull F d (grade.smooth.of_le le_top)).trans
  by_cases lower:d<toll
  · rw [grade.vanish d lower,norm_zero]; exact nonneg
  · let e:=d-toll
    have entry:e≤p:=by dsimp [e]; omega
    have sum:e+toll=d:=by dsimp [e]; omega
    have h:=WilsonEmittedFiledThermalGerm.original V Z c₁ c₂ u left right A B entry sameV sameZ issued scheduled
    exact sum ▸ h.trans (price e (sum ▸ live))
end YM.Integration.WilsonEmittedFiledMixedWindow
