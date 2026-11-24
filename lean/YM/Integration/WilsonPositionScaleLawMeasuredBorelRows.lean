import YM.Integration.WilsonPositionScaleLawMeasuredBorel
import YM.Integration.WilsonPositionScaleLawMeasuredArms
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredBorelRows
open Function Filter Set Finset PowerSeries Maxwell XSpace XSpace.Normalize
open FVA2 FVA2.Register FVA2.Scale FVA2.Arrival MS MS.Land MS.Fleet
open Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot PhysicalNext.Repeat.Legato
open WilsonPositionScaleLawMeasuredSection (clipped)
open WilsonPositionProgramTrialPublicJointPivotForecast (forecast)
open WilsonPositionProgramTrialPublicJointPivotWeights (salary)
open WilsonPositionScaleLawMeasuredExperiment (peak atMost)
open WilsonPositionHomogeneousNear (field)
open scoped Topology BigOperators Classical
variable {G:Gauge}(Z:WilsonPrescription G) {hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ:Prescription (Press.portDeck G)}
    {b:Bool} (H:Main.Match Z hG M σ b) (ν:ℝ) {d n:ℕ}

include H in
theorem uniform (q:ℕ)(φ:Test n) : ∃C:ℝ,0≤C ∧ ∀ᶠu:ℝ in 𝓝[>] 0,∀v:Fin n→Sec G d,
    ‖forecast Z M ν d q u n φ (fun i=>stand (field Z d u) (v i))-clipped Z M ν d q u n φ v‖
        ≤(∏i,salary (v i))*(C*u^(q+1)) :=by
  let basis:=Module.finBasis ℝ (Sec G d)
  choose K positive fees using fun a:Fin n→Pin G d=>WilsonPositionScaleLawMeasuredBorel.point Z M H ν q φ (fun i=>basis (a i))
  let C:=max 0 (peak K)
  have hC:0≤C:=le_max_left .. 
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_all.mpr fees,self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with u income pos v
  let P:=recruit (stand (field Z d u)) (forecast Z M ν d q u)
  apply WilsonPositionProgramTrialPublicJointPivotWeights.paid (P n φ) (clipped Z M ν d q u n φ) v
    (mul_nonneg hC (pow_nonneg (le_of_lt pos) _))
  intro a
  exact (income a).trans (mul_le_mul_of_nonneg_right ((atMost K a).trans (le_max_right ..)) (pow_nonneg (le_of_lt pos) _))

variable {R:Run G}{o:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family o S) (J:ℝ→tower S)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "arm" => WilsonPositionScaleLawMeasuredArms.arm Z F J

include H in
theorem rested (q:ℕ)(φ:Test n)(clock:Tendsto θ trail (𝓝[>] 0)) :
    ∃C:ℝ,0≤C ∧ ∀ᶠr in trail,∀v:Fin n→Sec G d,
      ‖forecast Z M ν d q (θ r) n φ (fun i=>arm r (v i))-clipped Z M ν d q (θ r) n φ v‖
      ≤(∏i,salary (v i))*(C*(θ r)^(q+1)) :=by
  obtain ⟨C,hC,fees⟩:=uniform Z M H ν (d:=d) q φ
  have near:Tendsto θ trail (𝓝 0):=clock.mono_right nhdsWithin_le_nhds
  refine ⟨C,hC,?_⟩
  filter_upwards [clock.eventually fees,near.eventually (WilsonPositionHomogeneousNear.invertible Z d)] with r issued fit v
  simp_rw [WilsonPositionScaleLawMeasuredArms.fitted Z F J r fit]
  exact issued v
end YM.Integration.WilsonPositionScaleLawMeasuredBorelRows
