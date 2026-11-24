import YM.Integration.WilsonPositionScaleLawMeasuredFiniteImage
import YM.Integration.WilsonPositionScaleLawMeasuredBorelRows
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredTestTape
open Function Filter Set Finset PowerSeries Maxwell XSpace XSpace.Normalize
open FVA2 FVA2.Register FVA2.Scale FVA2.Arrival MS MS.Land MS.Fleet
open WilsonPositionScaleLawMeasuredSection (clipped)
open WilsonPositionProgramTrialPublicJointPivotForecast (forecast)
open WilsonPositionHomogeneousNear (field)
open scoped Topology BigOperators Classical
variable {G:Gauge}(Z:WilsonPrescription G) {hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ:Prescription (Press.portDeck G)}
    {b:Bool} (H:Main.Match Z hG M σ b) (ν:ℝ) {d n:ℕ}
abbrev Tag (G:Gauge)(d q n:ℕ):=Fin (q+1)×(Fin n→Pin G d)
local notation "T" => Measure.adjust Z.scheme Z.criterion d
local notation "R" => Reg.Faith.reports ν Z.criterion M d

def tape (d q n:ℕ):Test n→ₗ[ℂ](Tag G d q n→ℂ) where
  toFun φ a:=Reg.Faith.reports ν Z.criterion M d a.1 n φ (fun i=>Module.finBasis ℝ (Sec G d) (a.2 i))
  map_add' x y:=by funext a; simp only [map_add,add_apply,Pi.add_apply]
  map_smul' c x:=by funext a; simp only [map_smul,smul_apply,Pi.smul_apply,RingHom.id_apply]

def debt (q:ℕ)(v:Fin n→Sec G d)(u:ℝ):Test n→ₗ[ℂ]ℂ where
  toFun φ:=forecast Z M ν d q u n φ (fun i=>stand (field Z d u) (v i))-clipped Z M ν d q u n φ v
  map_add' x y:=by simp only [map_add,add_apply];ring
  map_smul' c x:=by simp only [map_smul,smul_apply,RingHom.id_apply,smul_sub]

theorem factor (q:ℕ)(v:Fin n→Sec G d)(u:ℝ)(φ:Test n)(zero:tape Z M ν d q n φ=0):debt Z M ν q v u φ=0:=by
  have registered (k:ℕ)(room:k≤q)(z:Fin n→Sec G d):R k n φ z=0:=by
    apply norm_le_zero_iff.mp
    have pay:=WilsonPositionProgramTrialPublicJointPivotWeights.paid (R k n φ) (0:MultilinearMap ℂ (fun _:Fin n=>Sec G d) ℂ) z (e:=0) le_rfl
    have all:∀b,‖WilsonPhysicalPositionTargetRows.rows (R k n φ) b-WilsonPhysicalPositionTargetRows.rows (0:MultilinearMap ℂ (fun _:Fin n=>Sec G d) ℂ) b‖≤0:=by
      intro a
      have print:=congrFun zero (⟨k,by omega⟩,a)
      change R k n φ (fun i=>Module.finBasis ℝ (Sec G d) (a i))=0 at print
      simp only [WilsonPhysicalPositionTargetRows.rows,zero_apply,sub_zero,print,norm_zero,le_refl]
    simpa only [zero_apply,sub_zero,mul_zero] using pay all
  have realmZero(k:ℕ)(room:k≤q):realm T R k n φ v=0:=by
    rw [WilsonPositionScaleLawMeasuredWord.atOrder T R φ v room]
    apply sum_eq_zero
    intro w _
    have part:=registered (w none).val (by have h:=(w none).isLt;omega)
      (fun i=>coeff (w (some i)).val T (v i))
    simp only [WilsonPositionScaleLawMeasuredWord.node,part,ite_self]
  change forecast Z M ν d q u n φ _ - clipped Z M ν d q u n φ v=0
  rw [WilsonPositionProgramTrialPublicJointPivotForecast.value,WilsonPositionScaleLawMeasuredSection.value]
  have x:(∑k∈range (q+1),(u:ℂ)^k * R k n φ (fun i=>stand (field Z d u) (v i)))=0:=by
    apply sum_eq_zero
    intro k hk
    rw [registered k (by have a:=mem_range.mp hk;omega),mul_zero]
  have y:(∑k∈range (q+1),(u:ℂ)^k * WilsonPositionScaleLawMeasuredSection.reports Z M ν d k n φ v)=0:=by
    apply sum_eq_zero
    intro k hk
    rw [WilsonPositionScaleLawMeasuredSection.reports,realmZero k (by have a:=mem_range.mp hk;omega),mul_zero]
  rw [x,y,sub_zero]

include H in
theorem original (q:ℕ)(v:Fin n→Sec G d):∃C:ℝ,0≤C ∧ ∀ᶠu:ℝ in 𝓝[>] 0,∀φ:Test n,
      ‖debt Z M ν q v u φ‖≤(C*‖tape Z M ν d q n φ‖)*u^(q+1):=by
  apply WilsonPositionScaleLawMeasuredFiniteImage.original (tape Z M ν d q n) (debt Z M ν q v)
  · filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with u hu
    exact pow_nonneg (le_of_lt hu) _
  · exact factor Z M ν q v
  · exact fun φ=>WilsonPositionScaleLawMeasuredBorel.point Z M H ν q φ v
end YM.Integration.WilsonPositionScaleLawMeasuredTestTape
