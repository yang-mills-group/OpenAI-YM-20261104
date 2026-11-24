import YM.Integration.WilsonInvariantActionCapturedPoints
import YM.Integration.WilsonInvariantActionPromotedRegular

/-! Smear the genuine separated early capture, retaining the original 
upper cutoff and period order and the original signed two-point test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionCapturedProfile
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Spec
open FullVolume Table Climb Trace.Pilot RG17 Next.UVStress PhysMS Next.Rank
open RGComparison.Core16 OPE OPE.Therm PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12 WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Pert.Asymptotics WilsonInvariantActionPosition WilsonInvariantActionIntegratedPair WilsonInvariantActionPromotedPair
open WilsonInvariantActionCapturedCovariance WilsonInvariantActionCapturedPoints
open private volume_bill from YM.Integration.WilsonInvariantActionPromotedPair
open private coupling_bound from YM.Integration.WilsonInvariantActionPromotedRegular
open scoped Topology BigOperators Classical
universe u
variable {G:Gauge} (R:Run G) {k N per:ℕ} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (L:Layout F)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

def earlier (h:k≤N) (v:Fin 2→R.family.label 4) (φ:Test 2):ℂ:=
  ∑x:Fin 2→Site (R.family.side N per),WilsonExternalMeshMass.charge R.family φ x * regularCov R h v x

theorem filed (simple:G.Simple) {δ₀:ℝ} {T:Campaign R} (W:Campaign.Pillars R T)
    (funded:FundedOriginalProperties.{u} simple δ₀ W) (subsidy:WilsonReportColumnSubsidy.Eligible R.kit)
    (pace:WilsonWindowReportingPace.Slow R.kit) (E:Services R.family f S) {B:ℕ} (hB:0<B)
    (level:L.level=WilsonMeasuredWindow.stop (A) simple B)
    {g:ℝ→ℝ} (coupling:Coupling G g) {s:ℕ} (hs:1 ≤ s) (e q:ℕ) (φ:Test 2) {ε:ℝ} (he:0<ε):
    ∀ᶠ r in trail,let m:=L.level r;let k:=berth R s m
     ∀(hr:0<r),R.family.ref 4 ≤ m →∀v:Fin 2→R.family.label 4,
       (∀i N per,m ≤ N →quota R.family 4 m N per (atRef L 4 r (N,per) (v i))≤R.family.S.a m^4*β m^e) →
       ∀ᶠ z:ℕ×ℕ in L.lens,∀h:k<z.1,let w:=fun i=>atRef L 4 r z (v i)
       ‖tested R (p:=z.2) h.le (w 0) (w 1) (dilate hr φ)-earlier R (per:=z.2) h.le w (dilate hr φ)‖≤ε*(g r)^q:=by
  let t:=(s+2)*5+e;let M:ℝ:=(∫x,‖φ x‖)+1
  let fee:=WilsonReportSeparatedMoments.fee census both (q+1)
  have fp:0≤fee:=WilsonReportSeparatedMoments.fee_nonneg census both (q+1)
  have mp:0<M:=by dsimp only [M];positivity
  let C:=M*fee*2^(2*(q+1))
  have shrink:Tendsto (fun r=>C*(g r)^(q+2)) trail (𝓝 0):=by
    have z: Tendsto g trail (𝓝 0):=coupling.conforms simple
    simpa using (tendsto_const_nhds (x:=C)).mul (z.pow (q+2))
  have rate:=shrink.eventually (gt_mem_nhds he)
  have grow:Tendsto L.level trail atTop:=by rw [level];exact WilsonMeasuredWindow.stop_tendsto _ simple B hB
  have market:=grow.eventually (WilsonInvariantActionPromotedQuota.price R simple pace F L E s 4 e)
  have temperature:=(WilsonPhysicalCutoffCurrency.temperature R simple pace hB g coupling).eventually
    (lt_mem_nhds (show (1/2:ℝ)<1 by norm_num))
  have sites:=WilsonInvariantActionCapturedPoints.purchased R simple W funded subsidy pace hB hs t (q+1) φ
  rw [←level] at sites
  filter_upwards [market,temperature,sites,rate,coupling.positive] with r money hot points affordable gp
  let m:=L.level r; let k:=berth R s m
  dsimp only
  intro hr ref v receipts
  have heat:1/2<β m*(g r)^2:=by simpa only [m,level] using hot
  have mk:m≤k:=(arrival R s m).1.le
  let ψ:=dilate hr φ
  have signed:=(WilsonExternalMeshMass.funded R.family f ψ ψ.continuous ψ.hasCompactSupport
      (show (0:ℝ)<1 by norm_num)).filter_mono L.certified
  filter_upwards [signed] with z total
  intro live
  let w:=fun i=>atRef L 4 r z (v i)
  let c:=fun x:Fin 2→Site (R.family.side z.1 z.2)=>WilsonExternalMeshMass.charge R.family ψ x
  let obs x:=posterior R (someSlices (A) z.2) live.le (w 0) (w 1) (parents R live.le x)
  let regular:=regularCov R (per:=z.2) live.le w
  let cost:=fee*(2*g r)^(2*(q+1))
  have cp:0≤cost:=by dsimp only [cost];positivity
  have pay (i):quota R.family 4 k z.1 z.2 (w i)≤R.family.S.a k^4*β k^t:=by
    have bought:=money rfl (show (0:ℝ)≤1 by norm_num) (v i) ref (fun N p hN=>by simpa only [mul_one] using receipts i N p hN) z.1 z.2 live.le
    simpa only [mul_one] using bought
  have realrate:regulatorRun R.family z.1 z.2 k≤2*g r:=coupling_bound R simple mk live.le gp heat
  have all (x):‖c x*(obs x-regular x)‖≤‖c x‖*cost:=by
    by_cases hx:c x=0
    · simp only [hx,zero_mul,norm_zero,le_refl]
    · rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have single: ‖obs x-regular x‖≤fee*(regulatorRun R.family z.1 z.2 k)^(2*(q+1)):=
        points hr z.1 z.2 live x hx w pay
      apply single.trans
      dsimp only [cost,fee]
      have nonneg:0≤regulatorRun R.family z.1 z.2 k:=by unfold regulatorRun;positivity
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ nonneg realrate _) fp
  have mass:∑x,‖c x‖≤M:=by simpa only [c,ψ,M,volume_bill] using total
  change ‖(∑x,c x*obs x)-(∑x,c x*regular x)‖≤ε*(g r)^q
  calc
    _=‖∑x,c x*(obs x-regular x)‖:=by simp only [mul_sub,sum_sub_distrib]
    _≤∑x,‖c x*(obs x-regular x)‖:=norm_sum_le _ _
    _≤∑x,‖c x‖*cost:=sum_le_sum fun x _=>all x
    _=(∑x,‖c x‖)*cost:=(sum_mul ..).symm
    _≤M*cost:=mul_le_mul_of_nonneg_right mass cp
    _=(C*(g r)^(q+2))*(g r)^q:=by
      dsimp only [C,cost];rw [mul_pow,show 2*(q+1)=(q+2)+q by omega,pow_add (g r)];ring
    _≤ε*(g r)^q:=mul_le_mul_of_nonneg_right affordable.le (pow_nonneg gp.le _)

end YM.Integration.WilsonInvariantActionCapturedProfile
