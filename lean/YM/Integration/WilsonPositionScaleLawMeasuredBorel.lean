import YM.Integration.WilsonPositionScaleLawMeasuredAdjustment
import YM.Integration.WilsonPositionScaleLawMeasuredExperiment

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredBorel
open Function Filter Set Finset PowerSeries Maxwell XSpace XSpace.Normalize
open FVA2 FVA2.Register FVA2.Scale FVA2.Arrival MS MS.Land MS.Fleet
open WilsonPositionScaleLawGuardHomePrint (tab)
open WilsonPositionScaleLawMeasuredSection (clipped)
open WilsonPositionProgramTrialPublicJointPivotForecast (forecast)
open WilsonPositionHomogeneousNear (field)
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}(Z:WilsonPrescription G) {hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ:Prescription (Press.portDeck G)}
    {b:Bool} (H:Main.Match Z hG M σ b) (ν:ℝ) {d n:ℕ}

private theorem base (d q:ℕ):tab Z d q 0=0 :=by
  rw [tab,sum_eq_single 0]
  · simp [WilsonPositionHomogeneousCoefficients.letter]
  · intro k _ hk
    simp [zero_pow hk]
  · simp

include H in
theorem point (q:ℕ)(φ:Test n)(v:Fin n→Sec G d) :
    ∃C:ℝ,0≤C ∧ ∀ᶠu:ℝ in 𝓝[>] 0,
      ‖forecast Z M ν d q u n φ (fun i=>stand (field Z d u) (v i))-clipped Z M ν d q u n φ v‖≤C*u^(q+1) :=by
  let U:=fun u:ℝ=>guide G d (field Z d u)
  let Q:=fun z:MoveSpace G d×ℝ=>forecast Z M ν d q z.2 n φ (fun i=>Fray.box z.1 (v i))
  have smooth:ContDiffAt ℝ 1 Q (0:MoveSpace G d×ℝ):=
    ((WilsonPositionScaleLawMeasuredMoves.ordinary Z M ν d q n φ v).of_le (by norm_num)).contDiffAt
  obtain ⟨L,K,hK,lip⟩:=smooth.exists_lipschitzOnWith
  obtain ⟨A,hA,expansion⟩:=WilsonPositionHomogeneousNear.expansion Z d q
  let fee:=WilsonPositionScaleLawMeasuredAdjustment.salary Z M ν q φ v
  have feePos:0≤fee:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  refine ⟨L*A+fee,add_nonneg (mul_nonneg L.coe_nonneg hA) feePos,?_⟩
  have pcont:Continuous (tab Z d q):=by unfold tab; fun_prop
  have small:Tendsto (tab Z d q) (𝓝 0) (𝓝 0):=by
    simpa only [base Z d q] using pcont.tendsto 0
  have realPath:Tendsto (fun u:ℝ=>(U u,u)) (𝓝[>] 0) (𝓝 (0:MoveSpace G d×ℝ)):=
    ((WilsonPositionHomogeneousNear.near Z d).prodMk_nhds tendsto_id).mono_left nhdsWithin_le_nhds
  have polyPath:Tendsto (fun u:ℝ=>(tab Z d q u,u)) (𝓝[>] 0) (𝓝 (0:MoveSpace G d×ℝ)):=
    (small.prodMk_nhds tendsto_id).mono_left nhdsWithin_le_nhds
  filter_upwards [realPath.eventually hK,polyPath.eventually hK,expansion,
    self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0),(gt_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with u live poly price pos size
  change 0<u at pos
  have near:‖U u-tab Z d q u‖≤A*u^(q+1):=by
    exact price
  have continuity:‖Q (U u,u)-Q (tab Z d q u,u)‖≤L*‖U u-tab Z d q u‖:=by
    have same:dist (U u,u) (tab Z d q u,u)=dist (U u) (tab Z d q u):=by
      rw [Prod.dist_eq,dist_self,max_eq_left dist_nonneg]
    simpa only [same,dist_eq_norm] using
      (lipschitzOnWith_iff_dist_le_mul.mp lip) _ live _ poly
  have stated:=WilsonPositionScaleLawMeasuredAdjustment.original Z M H ν q u (by simpa only [abs_of_pos pos] using size.le) φ v
  rw [abs_of_pos pos] at stated
  have leg:Fray.box (U u)=stand (field Z d u):=by
    change stand ((guide G d).symm (guide G d (field Z d u)))=_
    rw [LinearEquiv.symm_apply_apply]
  change ‖forecast Z M ν d q u n φ (fun i=>stand (field Z d u) (v i))-_‖≤_
  rw [←leg]
  calc
    _≤‖Q (U u,u)-Q (tab Z d q u,u)‖+‖Q (tab Z d q u,u)-clipped Z M ν d q u n φ v‖:=by
      simpa only [dist_eq_norm] using dist_triangle (Q (U u,u)) (Q (tab Z d q u,u)) (clipped Z M ν d q u n φ v)
    _≤(L:ℝ)*(A*u^(q+1))+u^(q+1)*fee:=add_le_add (continuity.trans (mul_le_mul_of_nonneg_left near L.coe_nonneg)) stated
    _=_:=by ring

end YM.Integration.WilsonPositionScaleLawMeasuredBorel
