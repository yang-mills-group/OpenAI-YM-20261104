import YM.Integration.WilsonMatrixTicketLanesRegisteredPair
import YM.Integration.WilsonMatrixTicketLanesConnectedWitness
import YM.Integration.WilsonMatrixOriginalParentPurchase

/-! The original finite smooth profile, with the whole earlier medium and both one-point
contributions, permits removing the actual local flags at every perturbative order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixTicketLanesRegisteredProfile
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
local notation "β" => R.family.path.levels.clock.hatBeta

def point {k N per:ℕ} (live:k ≤ N) (v:Fin 2→R.family.label 4) (x:Fin 2→Site (R.family.side N per)):ℂ:=
  let o:=fun i=>(R.family.S.toDepth live per).parent (x i)
  WilsonInvariantActionRegisteredReturn.pair (fun h=>∫V,h V ∂scene R.family.path N per k)
    (unmaskedEarlier R k N per live (v 0) (o 0)) (unmaskedEarlier R k N per live (v 1) (o 1))

def unmaskedProfile {k N per:ℕ} (live:k ≤ N) (v:Fin 2→R.family.label 4) (φ:Test 2):ℂ:=
  ∑x:Fin 2→Site (R.family.side N per),WilsonExternalMeshMass.charge R.family φ x*point R live v x

theorem tested (simple:G.Simple) (Y:Poetry R.family.path.levels) (pace:WilsonWindowReportingPace.Slow R.kit)
    {B:ℕ} (wide:17 ≤ B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    (chosen:U ≤ L.lens) {g:ℝ→ℝ} (coupling:Coupling G g) (e q:ℕ) (φ:Test 2) {ε:ℝ} (ep:0<ε):
    ∀ᶠ r in trail,let m:=L.level r;∀hr:0<r,∀ᶠ z:ℕ×ℕ in U,∃live:m<z.1,
    ∀v:Fin 2→R.family.label 4,(∀i,quota R.family 4 m z.1 z.2 (v i) ≤ R.family.S.a m^4*β m^e)→
      ‖WilsonInvariantActionCapturedProfile.earlier R (per:=z.2) live.le v (dilate hr φ)-
        unmaskedProfile R (per:=z.2) live.le v (dilate hr φ)‖ ≤ ε*(g r)^q:=by
  let M:ℝ:=(∫x,‖φ x‖)+1
  have Mp:0<M:=by dsimp [M];positivity
  let η:=ε/(M*2^q)
  have ηp:0<η:=div_pos ep (mul_pos Mp (pow_pos zero_lt_two _))
  have table:=WilsonMatrixTicketLanesRegisteredPair.original R F L simple Y pace (2*e) q
    (D:=(2:ℝ)^e) (pow_nonneg zero_le_two _) ηp
  have grow:Tendsto L.level trail atTop:=by rw [level];exact WilsonMeasuredWindow.stop_tendsto _ simple B (by omega)
  have clock:=WilsonPhysicalCutoffCurrency.band R simple pace (B:=B) (by omega) g coupling
  filter_upwards [grow.eventually table,grow.eventually_ge_atTop (R.family.ref 4),clock] with r sale age band
  dsimp only []
  intro hr
  let m:=L.level r
  have future:∀ᶠz:ℕ×ℕ in f.fuse,m<z.1:=by
    change ∀ᶠ_:ℕ in atTop,∀ᶠ j:ℕ in atTop,m<f.mesh j
    exact .of_forall fun _=>f.mesh.cofinal.eventually_gt_atTop m
  let ψ:=dilate hr φ
  have volume:=(WilsonExternalMeshMass.funded R.family f ψ ψ.continuous ψ.hasCompactSupport one_pos).filter_mono
    (chosen.trans L.certified)
  filter_upwards [future.filter_mono (chosen.trans L.certified),volume] with z later bank
  refine ⟨later,?_⟩
  intro v costs
  let g₀:=regulatorRun R.family z.1 z.2 m
  have gx:0 ≤ g₀:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have paid (i:Fin 2):RG12.mass R.family 4 (entry R 4 m z.1 z.2 (v i)) ≤ (2:ℝ)^e/g₀^(2*e):=by
    rw [cost R F L 4 m z.1 z.2 age later.le]
    have pos:0<R.family.S.a m^4:=pow_pos (R.family.S.a_pos m) _
    calc
      _ ≤ (R.family.S.a m^4)⁻¹*(R.family.S.a m^4*β m^e):=
        mul_le_mul_of_nonneg_left (costs i) (inv_nonneg.mpr pos.le)
      _=β m^e:=by rw [←mul_assoc,inv_mul_cancel₀ pos.ne',one_mul]
      _ ≤ _:=WilsonMatrixTicketLanesRegisteredLoss.cutoff R later.le e
  let charge (x:Fin 2→Site (R.family.side z.1 z.2)):=WilsonExternalMeshMass.charge R.family ψ x
  let raw:=WilsonInvariantActionCapturedPoints.regularCov R (per:=z.2) later.le v
  let openRow:=point R (per:=z.2) later.le v
  have diff (x):‖raw x-openRow x‖ ≤ η*g₀^q:=
    sale z.1 later.le z.2 age (v 0) (v 1) _ _ (paid 0) (paid 1)
  have mass:∑x,‖charge x‖ ≤ M:=by simpa only [charge,ψ,M,volume_bill φ hr] using bank
  have coarse:g₀ ≤ 2*g r:=by
    simpa only [g₀,m,level] using (band z.1 z.2 (by simpa only [m,level] using later.le)).2
  change ‖(∑x,charge x*raw x)-(∑x,charge x*openRow x)‖ ≤ _
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑x,‖charge x*raw x-charge x*openRow x‖:=norm_sum_le _ _
    _ ≤ ∑x,‖charge x‖*(η*g₀^q):=Finset.sum_le_sum fun x _=>by
      rw [←mul_sub,norm_mul];exact mul_le_mul_of_nonneg_left (diff x) (norm_nonneg _)
    _ ≤ M*(η*g₀^q):=(Finset.sum_mul ..).symm.le.trans
      (mul_le_mul_of_nonneg_right mass (mul_nonneg ηp.le (pow_nonneg gx _)))
    _ ≤ M*(η*(2*g r)^q):=mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ gx coarse q) ηp.le) Mp.le
    _=ε*(g r)^q:=by dsimp [η];rw [mul_pow];field_simp [Mp.ne']

theorem on_row (simple:G.Simple) {ρ:ℝ} {T:Campaign R} (W:Campaign.Pillars R T)
    (funded:FundedOriginalProperties.{u} simple ρ W) (pace:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F J) (obey:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (chosen:U ≤ L.lens) {B:ℕ} (wide:17 ≤ B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    {δ g:ℝ→ℝ} (coupling:Coupling G g) (D:Profiles R 4) (j:D.probes.index) (v₀:(standard R.family.labels).Ref 4)
    (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀) (e:ℕ)
    (deposit:ℝ→RG17.Free R.family 4→R.family.label 4) (χ:ℂ→L[ℝ]ℝ) (σ:ℝ)
    (record:Row (H:=H) (U:=U) F J Z L δ g D j v₀ hs e deposit χ σ):
    let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
    let v:=(Bel R.family.book).project 4 v₀
    let a:=fun r=>deposit r (stepField R.family)
    let b:=fun r=>deposit r (freeInput F J Z 4 r v)
    ∀q:ℕ,∀ε>0,∀ᶠr in trail,∀hr:0<r,∀ᶠz:ℕ×ℕ in U,∃live:L.level r<z.1,
      let marks:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
      ‖WilsonInvariantActionCapturedProfile.earlier R (per:=z.2) live.le marks (dilate hr φ)-
        unmaskedProfile R (per:=z.2) live.le marks (dilate hr φ)‖ ≤ ε*(g r)^q:=by
  let v:=(Bel R.family.book).project 4 v₀
  let a:=fun r=>deposit r (stepField R.family)
  let b:=fun r=>deposit r (freeInput F J Z 4 r v)
  let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
  have cover:=at_inputs F J Z L lead obey simple (by omega :0<B) level e deposit v record.2.2.2.2.2.2.2.1
  dsimp only []
  intro q ε ep
  filter_upwards [tested R F L simple funded.2.1.paid.stoves pace wide level chosen coupling (e+1) q φ ep,cover]
    with r sale cost
  intro hr
  filter_upwards [sale hr] with z bill
  obtain ⟨live,hv⟩:=bill
  let w:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
  refine ⟨live,hv w fun i=>?_⟩
  dsimp only [w];rw [on_two];exact cost i z.1 z.2 live.le

end YM.Integration.WilsonMatrixTicketLanesRegisteredProfile
