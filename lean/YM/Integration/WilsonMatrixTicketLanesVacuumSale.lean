import YM.Integration.WilsonMatrixTicketLanesVacuumPanel
import YM.Integration.WilsonMatrixTicketLanesRegisteredProfile

/-! Original reporting prices pay the two earlier covariance terms and the complete signed variation of the measured pair at the requested continuum power. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixTicketLanesVacuumSale
open Filter Function Set Finset MeasureTheory Lattice Wilson RG Tree Precision RG17 Source Marker Extraction Extraction.Order Spec
open Table Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm Next.UVStress
open PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register Pert.Asymptotics
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionSpectatorPrices WilsonInvariantActionCalibratedColumn
open Trace.Sundial WilsonLimitConstruction WilsonMatrixOriginalEarlierPanel WilsonInvariantActionPairCovariance
open WilsonMatrixTicketLanesRegulatorColumn WilsonMatrixTicketLanesRegisteredCovariance
open private volume_bill from YM.Integration.WilsonInvariantActionPromotedPair
open private at_inputs on_two from YM.Integration.WilsonMatrixOriginalParentPurchase
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S)
  (J:ℝ→tower S) (Z:WilsonPrescription G) {H:(Bel R.family.book).Hierarchy} (L:Layout F)
  {U:Filter (ℕ×ℕ)}
open private normPrice normPrice_pos amount from YM.Integration.WilsonMatrixTicketLanesRegisteredPair
open WilsonInvariantActionPriorHearing WilsonMatrixTicketLanesVacuumPanel
local notation "β" => R.family.path.levels.clock.hatBeta

theorem tested (simple:G.Simple) (pace:WilsonWindowReportingPace.Slow R.kit)
    {B:ℕ} (wide:17≤B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    (chosen:U≤L.lens) {g:ℝ→ℝ} (coupling:Coupling G g) (e q:ℕ) (φ:Test 2) {ε:ℝ} (ep:0<ε):
    ∃η>0,∃p:ℕ,∀ᶠr in trail,∀hr:0<r,∀ᶠz:ℕ×ℕ in U,
    ∃k,L.level r=k+1 ∧ ∃live:k+1≤z.1,∃birth:R.family.ref 4≤k+1,
    ∀v:Fin 2→R.family.label 4,(∀i,quota R.family 4 (k+1) z.1 z.2 (v i)≤R.family.S.a (k+1)^4*β (k+1)^e)→
    ∀χ:ℂ→L[ℝ]ℝ,χ=Complex.reCLM ∨ χ=Complex.imCLM→
    ∀w:(Fin 2→Site (R.family.side z.1 z.2))→ readings
      (Config G (R.family.side k z.2) × Config G (R.family.side (k+1) z.2)),
    (∀x,joint R live (WilsonMatrixTicketLanesVacuumIncome.absolute (w x))≤
      η*(regulatorRun R.family z.1 z.2 (k+1))^p)→
    ∀s:Kind,|signed R s live birth v (dilate hr φ) χ w|≤ε*(g r)^q:=by
  let D:ℝ:=(2:ℝ)^e
  let t:=2*e+4
  let K:=normPrice R*D
  let M:ℝ:=(∫x,‖φ x‖)+1
  have Kn:0≤K:=mul_nonneg (normPrice_pos R) (pow_nonneg zero_le_two _)
  have Mp:0<M:=by dsimp [M];positivity
  let denom:=24*(K*K+1)*M*2^q
  have dp:0<denom:=by dsimp [denom];positivity
  let η:=ε/denom
  have ηp:0<η:=div_pos ep dp
  refine ⟨η,ηp,q+(t+t),?_⟩
  have grow:Tendsto L.level trail atTop:=by rw [level];exact WilsonMeasuredWindow.stop_tendsto _ simple B (by omega)
  have clock:=WilsonPhysicalCutoffCurrency.band R simple pace (B:=B) (by omega) g coupling
  filter_upwards [grow.eventually (columns R simple pace),
    grow.eventually (WilsonMatrixTicketLanesReportedAccuracy.small R simple 1 zero_lt_one),
    grow.eventually_ge_atTop (R.family.ref 4),grow.eventually_ge_atTop 1,clock] with r column small born pos exchange
  intro hr
  obtain ⟨k,sk⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:L.level r≠0)
  have later:∀ᶠz:ℕ×ℕ in f.fuse,L.level r<z.1:=by
    change ∀ᶠ_:ℕ in atTop,∀ᶠj:ℕ in atTop,L.level r<f.mesh j
    exact .of_forall fun _=>f.mesh.cofinal.eventually_gt_atTop _
  let ψ:=dilate hr φ
  have volume:=(WilsonExternalMeshMass.funded R.family f ψ ψ.continuous ψ.hasCompactSupport one_pos).filter_mono
    (chosen.trans L.certified)
  filter_upwards [later.filter_mono (chosen.trans L.certified),volume] with z future bank
  have live:k+1≤z.1:=by omega
  have birth:R.family.ref 4≤k+1:=by omega
  refine ⟨k,sk,live,birth,?_⟩
  intro v costs χ select w source kind
  let c:=regulatorRun R.family z.1 z.2 (k+1)
  have cp:0<c:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))
  have paid (i:Fin 2):RG12.mass R.family 4 (entry R 4 (k+1) z.1 z.2 (v i))≤D/c^(2*e):=by
    rw [cost R F L 4 (k+1) z.1 z.2 birth live]
    have ap:0<R.family.S.a (k+1)^4:=pow_pos (R.family.S.a_pos _) _
    calc
      _≤(R.family.S.a (k+1)^4)⁻¹*(R.family.S.a (k+1)^4*β (k+1)^e):=mul_le_mul_of_nonneg_left (costs i) (inv_nonneg.mpr ap.le)
      _=β (k+1)^e:=by rw [←mul_assoc,inv_mul_cancel₀ ap.ne',one_mul]
      _≤_:=WilsonMatrixTicketLanesRegisteredLoss.cutoff R live e
  rw [sk] at column small
  have actual(i:Fin 2)(o):= (amount R F L live birth (small z.1 z.2 live) (column z.1 z.2 live)
    (v i) o (2*e) (paid i)).1
  have price:=WilsonMatrixTicketLanesVacuumPanel.tested R kind live birth v ψ χ select w
    (A:=K/c^t) (B:=K/c^t) (M:=η*c^(q+(t+t)))
    (div_nonneg Kn (pow_nonneg cp.le _)) (div_nonneg Kn (pow_nonneg cp.le _)) (actual 0) (actual 1) source
  have mass:(∑x:Fin 2→Site (R.family.side z.1 z.2),‖WilsonExternalMeshMass.charge R.family ψ x‖)≤M:=by simpa only [ψ,M,volume_bill φ hr] using bank
  have date:k+1=WilsonMeasuredWindow.stop R.family.path.levels simple B r:=sk.symm.trans (congrFun level r)
  have coarse:c≤2*g r:=by
    change regulatorRun R.family z.1 z.2 (k+1)≤2*g r
    rw [date]
    exact (exchange z.1 z.2 (date ▸ live)).2
  have gm:0≤g r:=by linarith only [coarse,cp]
  calc
    _≤_:=price
    _≤(24*((K/c^t)*(K/c^t))*(η*c^(q+(t+t))))*M:=mul_le_mul_of_nonneg_left mass (by positivity)
    _=(24*(K*K)*η*M)*c^q:=by rw [pow_add c q,pow_add c t];field_simp [cp.ne']
    _≤(24*(K*K+1)*η*M)*(2*g r)^q:=by gcongr;linarith
    _=ε*(g r)^q:=by rw [mul_pow];dsimp [η,denom];field_simp [ne_of_gt Mp,show K*K+1≠0 by positivity]

end YM.Integration.WilsonMatrixTicketLanesVacuumSale
