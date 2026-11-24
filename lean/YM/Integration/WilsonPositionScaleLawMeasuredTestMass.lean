import YM.Integration.WilsonPositionScaleLawMeasuredTestTape
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredTestMass
open Function Filter Set Finset PowerSeries MeasureTheory Maxwell XSpace XSpace.Normalize
open FVA2 FVA2.Register FVA2.Scale FVA2.Arrival MS MS.Land MS.Fleet
open WilsonPositionScaleLawMeasuredTestTape (Tag tape debt)
open WilsonPositionScaleLawMeasuredExperiment (peak atMost mass)
open WilsonPositionScaleLawMeasuredSection (clipped)
open WilsonPositionProgramTrialPublicJointPivotForecast (forecast)
open WilsonPositionProgramTrialPublicJointPivotWeights (salary)
open WilsonPositionHomogeneousNear (field)
open scoped Topology BigOperators Classical
variable {G:Gauge}(Z:WilsonPrescription G) {hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ:Prescription (Press.portDeck G)}
    {b:Bool} (H:Main.Match Z hG M σ b) (ν:ℝ) {d n:ℕ}

private theorem smeared (φ:Test n)(f:Points n→ℂ)(C:ℝ)
    (bound:∀x∈tsupport (φ:Points n→ℂ),‖f x‖ ≤ C):
    ‖φ.applyTo f‖ ≤ mass φ*C:=by
  have integrable:Integrable (fun x:Points n=>φ x):=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  change ‖∫x,φ x*f x‖ ≤ (∫x,‖φ x‖)*C
  apply (norm_integral_le_of_norm_le (integrable.norm.mul_const C) (Eventually.of_forall (fun x=>?_))).trans
  · rw [integral_mul_const]
  · by_cases zero:φ x=0
    · simp [zero]
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (bound x (subset_tsupport _ zero)) (norm_nonneg _)

include H in
theorem charged (d q n:ℕ)(K:Set (Points n))(hc:IsCompact K)(clear:K ⊆ conf n):
    ∃B:ℝ,0 ≤ B ∧ ∀φ:Test n,tsupport (φ:Points n→ℂ) ⊆ K→‖tape Z M ν d q n φ‖ ≤ mass φ*B:=by
  let data:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  let source:=Jury.enrolled ν M Z.scheme Z.criterion σ hG data.Taylor data.still data.base (d:=d)
  have smooth:Jury.Thin (Measure.start Z.scheme Z.criterion d):=by
    simpa only [Facets.team_one] using (source.glance X).light
  let row:=fun (a:Tag G d q n) (x:Points n)=>Jury.fxt (Measure.start Z.scheme Z.criterion d) x a.1
    (fun i=>Module.finBasis ℝ (Sec G d) (a.2 i))
  choose B cap using fun a:Tag G d q n=>hc.exists_bound_of_continuousOn
    ((smooth n a.1 (fun i=>Module.finBasis ℝ (Sec G d) (a.2 i))).mono clear)
  let C:=max 0 (peak B)
  have c0:0 ≤ C:=le_max_left ..
  refine ⟨C,c0,?_⟩
  intro φ hφ
  have weight:0 ≤ mass φ:=integral_nonneg fun _=>norm_nonneg _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg weight c0)).mpr
  intro a
  change ‖Reg.Faith.reports ν Z.criterion M d a.1 n φ _‖ ≤ _
  rw [WilsonPositionProgramTrialPublicJointPivotForecast.prescribed Z M H ν]
  exact smeared φ (row a) C (fun x hx=>(cap a x (hφ hx)).trans ((atMost B a).trans (le_max_right ..)))

include H in
theorem original (q:ℕ)(K:Set (Points n))(hc:IsCompact K)(clear:K ⊆ conf n):
    ∃C:ℝ,0 ≤ C ∧ ∀ᶠu:ℝ in 𝓝[>] 0,∀φ:Test n,tsupport (φ:Points n→ℂ) ⊆ K→∀v:Fin n→Sec G d,
      ‖forecast Z M ν d q u n φ (fun i=>stand (field Z d u) (v i))-clipped Z M ν d q u n φ v‖
           ≤ (∏i,salary (v i))*((C*mass φ)*u^(q+1)):=by
  obtain ⟨B,hB,absolute⟩:=charged Z M H ν d q n K hc clear
  choose Kb hp prices using fun a:Fin n→Pin G d=>WilsonPositionScaleLawMeasuredTestTape.original Z M H ν q
    (fun i=>Module.finBasis ℝ (Sec G d) (a i))
  let A:=max (0:ℝ) (peak Kb)
  have hA:0 ≤ A:=le_max_left ..
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  filter_upwards [eventually_all.mpr prices,self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with u settled pos φ inside v
  change 0<u at pos
  have hu:0 ≤ u^(q+1):=pow_nonneg pos.le _
  have hφ:0 ≤ mass φ:=integral_nonneg fun _=>norm_nonneg _
  let P:=recruit (stand (field Z d u)) (forecast Z M ν d q u)
  apply WilsonPositionProgramTrialPublicJointPivotWeights.paid (P n φ) (clipped Z M ν d q u n φ) v
    (mul_nonneg (mul_nonneg (mul_nonneg hA hB) hφ) hu)
  intro a
  calc
    _ ≤ (Kb a*‖tape Z M ν d q n φ‖)*u^(q+1):=settled a φ
    _ ≤ (A*(mass φ*B))*u^(q+1):=mul_le_mul_of_nonneg_right
      (mul_le_mul ((atMost Kb a).trans (le_max_right ..)) (absolute φ inside) (norm_nonneg _) hA) hu
    _=_:=by ring
end YM.Integration.WilsonPositionScaleLawMeasuredTestMass
