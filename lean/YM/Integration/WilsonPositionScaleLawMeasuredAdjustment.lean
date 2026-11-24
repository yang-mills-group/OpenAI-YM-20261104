import YM.Integration.WilsonPositionScaleLawMeasuredWordExpansion
import YM.Integration.WilsonPositionScaleLawGuardHomePrint
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredAdjustment
open Function Filter Set Finset PowerSeries Maxwell XSpace XSpace.Normalize
open FVA2 FVA2.Register FVA2.Scale FVA2.Arrival MS MS.Land MS.Fleet
open WilsonPositionHomogeneousCoefficients (letter Warrant)
open WilsonPositionScaleLawGuardHomePrint (tab)
open WilsonPositionScaleLawMeasuredWordExpansion (leg)
open WilsonPositionScaleLawMeasuredWord (Word node)
open WilsonPositionProgramTrialPublicJointPivotForecast (forecast)
open scoped Topology BigOperators Classical
variable {G:Gauge} (Z:WilsonPrescription G) {hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ:Prescription (Press.portDeck G)}
    {b:Bool} (H:Main.Match Z hG M σ b) (ν:ℝ) {d n:ℕ}
local notation "T" => Measure.adjust Z.scheme Z.criterion d
local notation "R" => Reg.Faith.reports ν Z.criterion M d

theorem each (law:Warrant Z)(k:ℕ)(v:Sec G d) :
    coeff k T v=(if k=0 then v else 0)+(letter Z d k).val v :=by
  by_cases h:k=0
  · subst k
    have f:coeff 0 T=1:=(coeff_zero_eq_constantCoeff_apply _).trans (law.scheme d).scale.lead
    simp [f,WilsonPositionHomogeneousCoefficients.letter]
  · rw [if_neg h,zero_add,WilsonPositionHomogeneousCoefficients.positive Z law d h]

theorem polynomial (law:Warrant Z)(q:ℕ)(u:ℝ)(v:Sec G d):
    Fray.box (tab Z d q u) v=leg T q u v :=by
  let L:MoveSpace G d→ₗ[ℝ]Sec G d:=
    {toFun x:=((guide G d).symm x).val v
     map_add':=by intro a b;rw [map_add];rfl
     map_smul':=by intro a b;rw [map_smul];rfl}
  have single (k:ℕ): L (guide G d (letter Z d k))=(letter Z d k).val v:=by
    simp only [L,LinearMap.coe_mk,AddHom.coe_mk,LinearEquiv.symm_apply_apply]
  change v+L (tab Z d q u)=_
  rw [leg,Fin.sum_univ_eq_sum_range (fun k:ℕ=>(u:ℂ)^k • coeff k T v) (q+1),tab,map_sum]
  simp_rw [each Z law _ v,smul_add]
  rw [sum_add_distrib]
  have identity:(∑k∈range (q+1),(u:ℂ)^k • (if k=0 then v else 0))=v:=by
    rw [sum_eq_single 0]
    · simp
    · intro k _ hk
      rw [if_neg hk,smul_zero]
    · simp
  rw [identity]
  congr 1
  apply sum_congr rfl
  intro k _
  rw [map_smul,single,←Complex.ofReal_pow]
  rfl

def salary (q:ℕ)(φ:Test n)(v:Fin n→Sec G d) : ℝ :=
  ∑w:Word n q,‖node T R φ v w‖

include H in
theorem original (q:ℕ)(u:ℝ)(small:|u|≤1)(φ:Test n)(v:Fin n→Sec G d) :
    ‖forecast Z M ν d q u n φ (fun i=>Fray.box (tab Z d q u) (v i))-
      WilsonPositionScaleLawMeasuredSection.clipped Z M ν d q u n φ v‖≤|u|^(q+1)*salary Z M ν q φ v :=by
  rw [WilsonPositionProgramTrialPublicJointPivotForecast.value,WilsonPositionScaleLawMeasuredSection.value]
  simp_rw [polynomial Z (WilsonPositionHomogeneousCoefficients.purchased Z H)]
  have exactCost:=WilsonPositionScaleLawMeasuredWordExpansion.original T R q u small φ v
  rw [Fin.sum_univ_eq_sum_range (fun k:ℕ=>(u:ℂ)^k*R k n φ (fun i=>leg T q u (v i))) (q+1)] at exactCost
  exact exactCost
end YM.Integration.WilsonPositionScaleLawMeasuredAdjustment
