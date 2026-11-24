import YM.Integration.WilsonInvariantActionLogarithmicReturn
import YM.Integration.ActualRelativeProfileTrial
import YM.Integration.WilsonExteriorGeometry

/-! The conditional and lower connected laws on identical original parent sites of the signed finite test. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixOriginalMatchedSites
open Filter Function Set Finset MeasureTheory Lattice Cells Wilson RG RG17 Source Spec Extraction
open FullVolume Table Climb Trace.Pilot Next.UVStress Next.Rank
open RGComparison.Core16 OPE OPE.Therm PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12 WilsonLimitConstruction
open Pert.Asymptotics WilsonInvariantActionPosition WilsonInvariantActionIntegratedPair
open WilsonInvariantActionPromotedPair WilsonInvariantActionCapturedCovariance
open WilsonInvariantActionCapturedPoints WilsonInvariantActionCapturedProfile
open private volume_bill from YM.Integration.WilsonInvariantActionPromotedPair
open private coupling_bound from YM.Integration.WilsonInvariantActionPromotedRegular
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (L:Layout F) {U:Filter (ℕ×ℕ)}
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

/-- The independent relative trial puts a coarse parent at its literal embedded address,
even when the physical upper regulator for the trial is different from the panel's cutoff. -/
theorem wrapped {n b j N p:ℕ} (hb:b≤N) (hj:b≤j) (x:Fin n→Site (R.family.side N p))
    (i:Fin n) {r θ:ℝ} (hr:r≠0) (scale:Real.exp θ=r/R.family.S.a j):
    let y:=fun i=>(R.family.S.toDepth hb p).parent (x i)
    let placed:=fun i=>R.family.S.gridPoint b (lift (y i))
    wrap (R.family.side j p) (ActualRelativeProfileTrial.offsets (fun _:Unit=>θ)
      (fun _ k l=>placed k l/r) i ())=(R.family.S.toDepth hj p).embed (y i) :=by
  intro y placed
  have old:=ActualRelativeProfileTrial.wrapped_actual R (fun _:Unit=>j) (fun _=>θ) (fun _=>r)
    (fun _=>placed) () i p hr scale
  have zero:StressFlux.Matching.ceilSite R.family j p (0:E4)=0:=by
    unfold StressFlux.Matching.ceilSite
    convert map_zero (wrap (R.family.side j p)) using 1
    congr 1;funext l;simp
  have aligned:=WilsonExteriorGeometry.ceilSite_add_grid (C:=R.family) (p:=p) hj (0:E4) (lift (y i))
  rw [zero,zero_add,zero_add,location,dif_pos hj,wrap_lift] at aligned
  exact old.trans aligned

theorem filed (simple:G.Simple) {ρ:ℝ} {T:Campaign R} (W:Campaign.Pillars R T)
    (funded:FundedOriginalProperties.{u} simple ρ W) (subsidy:WilsonReportColumnSubsidy.Eligible R.kit)
    (pace:WilsonWindowReportingPace.Slow R.kit) {B:ℕ} (large:17≤B)
    (level:L.level=WilsonMeasuredWindow.stop (A) simple B) (chosen:U≤L.lens)
    {g:ℝ→ℝ} (coupling:Coupling G g) (e q:ℕ) (φ:Test 2) {ε:ℝ} (ep:0<ε):
    ∀ᶠr in trail,let m:=L.level r
    ∀hr:0<r,∀ᶠz:ℕ×ℕ in U,∀live:m<z.1,∀w:Fin 2→R.family.label 4,
    (∀i,quota R.family 4 m z.1 z.2 (w i)≤R.family.S.a m^4*(β m)^e) →
    ‖WilsonInvariantActionPromotedPair.tested R (p:=z.2) live.le (w 0) (w 1) (dilate hr φ)-
      earlier R (per:=z.2) live.le w (dilate hr φ)‖≤ε*(g r)^q:=by
  have hp:0<B:=by omega
  have grow:Tendsto L.level trail atTop:=by rw [level];exact WilsonMeasuredWindow.stop_tendsto _ simple B hp
  have sites:=WilsonInvariantActionLogarithmicGeometry.original R simple pace large φ
  rw [←level] at sites
  have payments:=grow.eventually (WilsonInvariantActionCapturedPoints.at_date R simple W funded subsidy
    (br:=1) (by decide) 1 e (q+1))
  have hot:=(WilsonPhysicalCutoffCurrency.temperature R simple pace hp g coupling).eventually
    (lt_mem_nhds (show (1/2:ℝ)<1 by norm_num))
  let M:ℝ:=(∫x,‖φ x‖)+1
  let fee:=WilsonReportSeparatedMoments.fee census both (q+1)
  let C:=M*fee*2^(2*(q+1))
  have fp:0≤fee:=WilsonReportSeparatedMoments.fee_nonneg census both _
  have rate:Tendsto (fun r=>C*(g r)^(q+2)) trail (𝓝 0):=by
    simpa using (tendsto_const_nhds (x:=C)).mul ((coupling.conforms simple).pow (q+2))
  filter_upwards [sites,payments,hot,coupling.positive,rate.eventually (gt_mem_nhds ep)]
    with r geometry promised heat gp small
  intro m hr
  let ψ:=dilate hr φ
  have total:=(WilsonExternalMeshMass.funded R.family f ψ ψ.continuous ψ.hasCompactSupport
    (show (0:ℝ)<1 by norm_num)).filter_mono (chosen.trans L.certified)
  filter_upwards [total] with z budget
  intro live w wages
  let c:=fun x:Fin 2→Site (R.family.side z.1 z.2)=>WilsonExternalMeshMass.charge R.family ψ x
  let hi:=fun x=>posterior R (someSlices (A) z.2) live.le (w 0) (w 1) (parents R live.le x)
  let lo:=regularCov R (per:=z.2) live.le w
  let cost:=fee*(2*g r)^(2*(q+1))
  have paid:1/2<β m*(g r)^2:=by simpa only [m,level] using heat
  have bound:regulatorRun R.family z.1 z.2 m≤2*g r:=coupling_bound R simple le_rfl live.le gp paid
  have all (x):‖c x*(hi x-lo x)‖≤‖c x‖*cost:=by
    by_cases hx:c x=0
    · simp only [hx,zero_mul,norm_zero,le_refl]
    let d:=WilsonInvariantActionSeparatedCells.gap R.family live.le x
    obtain ⟨lower,upper⟩:=geometry hr z.1 z.2 live.le x hx
    have value:=promised d lower (by simpa only [pow_one] using upper) z.1 z.2 live x
      (show d≤d∧d≤1*d by simp) w wages
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact value.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by unfold regulatorRun;positivity) bound _) fp)
  have amount:∑x,‖c x‖≤M:=by simpa only [c,M,ψ,volume_bill] using budget
  change ‖(∑x,c x*hi x)-(∑x,c x*lo x)‖≤ε*(g r)^q
  calc
    _=‖∑x,c x*(hi x-lo x)‖:=by simp only [mul_sub,sum_sub_distrib]
    _≤∑x,‖c x*(hi x-lo x)‖:=norm_sum_le _ _
    _≤∑x,‖c x‖*cost:=sum_le_sum fun x _=>all x
    _=(∑x,‖c x‖)*cost:=(sum_mul ..).symm
    _≤M*cost:=mul_le_mul_of_nonneg_right amount (by dsimp only [cost];positivity)
    _=(C*(g r)^(q+2))*(g r)^q:=by
      dsimp only [C,cost];rw [mul_pow,show 2*(q+1)=(q+2)+q by omega,pow_add (g r)];ring
    _≤ε*(g r)^q:=mul_le_mul_of_nonneg_right small.le (pow_nonneg gp.le _)

end YM.Integration.WilsonMatrixOriginalMatchedSites
