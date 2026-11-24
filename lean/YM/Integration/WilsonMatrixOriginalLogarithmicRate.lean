import YM.Integration.WilsonMatrixOriginalEarlierPanel
import YM.Integration.WilsonInvariantActionLogarithmicReturn

/-! One pair of submitted fields at the original reporting date, with its spatial and coupling errors. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixOriginalLogarithmicRate
open Filter Function Set MeasureTheory Lattice Wilson RG RG17 Source Marker Extraction Extraction.Order
open Table Spec Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionSpectatorPrices WilsonInvariantActionPairCovariance
open WilsonInvariantActionCalibratedColumn WilsonInvariantActionPosition WilsonInvariantActionCapturedProfile
open WilsonInvariantActionCapturedCovariance WilsonInvariantActionCapturedPoints WilsonInvariantActionIntegratedPair Pert.Asymptotics WilsonLimitConstruction
open WilsonMatrixOriginalEarlierPanel
open private coupling_bound from YM.Integration.WilsonInvariantActionPromotedRegular
open scoped Classical Topology BigOperators

variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→tower S) (Z:WilsonPrescription G) {H:(Bel R.family.book).Hierarchy}
    (L:Layout F) {U:Filter (ℕ×ℕ)} [U.NeBot] (chosen:U≤L.lens)
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "Λ" => RG16.Lambda R.family.path.levels

include chosen in
theorem profile_limit (cut:(N p:ℕ)→Fin (N+1)) (φ:Test 2) {r:ℝ} (hr:0<r)
    (live:R.family.ref 4≤L.level r) (a b:R.family.label 4):
    Tendsto (fun z:ℕ×ℕ=>profile R cut (atRef L 4 r z a) (atRef L 4 r z b) (dilate hr φ) z.1 z.2) U
      (𝓝 (tested (master L 4 r a) (master L 4 r b) r φ)) := by
  let a₀:=locatedRef L 4 r a
  let b₀:=locatedRef L 4 r b
  have moving:=WilsonMatrixOriginalFiledCovariance.moving F (chosen.trans L.certified) cut (dilate hr φ)
    _ _ a₀ b₀ (tendsRef (L:=L) (D:=4) (r:=r) chosen tendsto_const_nhds live)
      (tendsRef (L:=L) (D:=4) (r:=r) chosen tendsto_const_nhds live)
  have fixed:=(along (WilsonMatrixOriginalPolarReadout.ordered F cut φ hr a₀ b₀)).mono_left
    (chosen.trans L.certified)
  simpa only [sub_add_cancel,zero_add,a₀,b₀,payRef] using moving.add fixed

def Rate (B:ℕ) (g:ℝ→ℝ) (a b:ℝ→R.family.label 4) (φ:Test 2) (cov:ℝ→ℂ) : Prop :=
  ∃C:ℝ,0≤C ∧ ∀q:ℕ,∀ε>0,∀ᶠr in trail,let m:=L.level r
    ∀hr:0<r,∀ᶠz:ℕ×ℕ in U,∃live:m<z.1,
    let fields:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
    ‖earlier R (per:=z.2) live.le fields (dilate hr φ)-cov r‖≤C*(Λ m^B)⁻¹+ε*(g r)^q

private theorem cost {M D A b K h t s fee:ℝ} (m:0≤M) (hd:0≤D) (a:0≤A)
    (within:b≤K) (radius:0≤h) (t0:0≤t) (cap : t ≤ s) (pf:0≤fee) (q:ℕ):
    M*((2+8*D*(A*b))*h+fee*t^(2*(q+1)))≤
      M*(2+8*D*(A*K))*h+M*fee*s^(2*(q+1)) := by
  have core:2+8*D*(A*b)≤2+8*D*(A*K):=add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left within a) (by positivity))
  calc
    _≤M*((2+8*D*(A*K))*h+fee*s^(2*(q+1))):=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right core radius)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ t0 cap _) pf)) m
    _=_:=by ring

variable (lead:Leading F J) (paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) (simple:G.Simple)
    {ρ:ℝ} {T:Campaign R} (W:Campaign.Pillars R T) (funded:FundedOriginalProperties.{u} simple ρ W)
    (subsidy:WilsonReportColumnSubsidy.Eligible R.kit) (pace:WilsonWindowReportingPace.Slow R.kit)
    {B:ℕ} (large:17≤B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)

include lead paid simple W funded subsidy pace large level chosen in
theorem filed {δ g:ℝ→ℝ} (coupling:Coupling G g) (D:Profiles R 4) (j:D.probes.index)
    (v₀:(standard R.family.labels).Ref 4)
    (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀)
    (e:ℕ) (deposit:ℝ→RG17.Free R.family 4→R.family.label 4) (χ:ℂ→L[ℝ]ℝ) (σ:ℝ)
    (record:Row (H:=H) (U:=U) F J Z L δ g D j v₀ hs e deposit χ σ):
    let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
    let v:=(Bel R.family.book).project 4 v₀
    let a:=fun r=>deposit r (stepField R.family)
    let b:=fun r=>deposit r (freeInput F J Z 4 r v)
    let cov:=fun r=>tested (J r 4 (stepField R.family)) (homogeneous F J Z r 4 v) r φ
    Rate (U:=U) F L B g a b φ cov := by
  intro φ v a b cov
  let M:ℝ:=(∫x,‖φ x‖)+1
  let α:=stepField R.family
  let K:=‖α‖+‖v‖+2
  have mp:0≤M:=by dsimp only [M];positivity
  have hα:‖α‖≤K:=by dsimp only [K];linarith [norm_nonneg v]
  have hv:‖v‖<K:=by dsimp only [K];linarith [norm_nonneg α]
  have bounded:∀ᶠr in trail,‖freeInput F J Z 4 r v‖≤K:=
    (WilsonOriginalCompensatedAnchor.field F J Z lead paid simple 4 v).norm.eventually (ge_mem_nhds hv)
  obtain ⟨D₀,Dp,account⟩:=WilsonInvariantActionLogarithmicReturn.filed F L J lead paid simple W
    funded subsidy pace large level φ
  let C:=M*(2+8*D₀*(‖α‖*K))
  have Cp:0≤C:=by dsimp only [C,K];positivity
  refine ⟨C,Cp,?_⟩
  intro q ε he
  let fee:=WilsonReportSeparatedMoments.fee census both (q+1)
  have fp:0≤fee:=WilsonReportSeparatedMoments.fee_nonneg census both (q+1)
  have hp:0<B:=by omega
  have grows:Tendsto L.level trail atTop:=by rw [level];exact WilsonMeasuredWindow.stop_tendsto _ simple B hp
  have warm:=(Next.Rank.Station.hat_rate R.family.path.levels simple).comp grows
  have hot:=(WilsonPhysicalCutoffCurrency.temperature R simple pace hp g coupling).eventually
    (lt_mem_nhds (show (1/2:ℝ)<1 by norm_num))
  let A:=M*fee*2^(2*(q+1))
  have vanish:Tendsto (fun r=>A*(g r)^(q+2)) trail (𝓝 0):=by
    simpa using (tendsto_const_nhds (x:=A)).mul ((coupling.conforms simple).pow (q+2))
  obtain ⟨_,_,_,_,_,_,_,market,_⟩:=record
  filter_upwards [account (e+1) (q+1),market,bounded,warm.eventually_ge_atTop K,
    grows.eventually_ge_atTop (R.family.ref 4),coupling.positive,hot,
    vanish.eventually (gt_mem_nhds (half_pos he))] with r price paid₀ bound top age gp heat small
  intro m hr
  let vv:Fin 2→RG17.Free R.family 4:=Fin.cons α (fun _=>freeInput F J Z 4 r v)
  let ww:=fun i=>deposit r (vv i)
  have pay (i:Fin 2) (N per:ℕ) (hn:m≤N):
      quota R.family 4 m N per (atRef L 4 r (N,per) (ww i))≤R.family.S.a m^4*β m^(e+1):=by
    have size:‖vv i‖≤β m:=by fin_cases i;exact hα.trans top;exact bound.trans top
    have issued:quota R.family 4 m N per (atRef L 4 r (N,per) (ww i))≤
        R.family.S.a m^4*(β m^e*‖vv i‖):=(paid₀ (vv i)).2 N per hn
    rw [pow_succ (β m)]
    exact issued.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left size
      (pow_nonneg (zero_lt_one.trans (R.family.path.levels.fits.delayed m)).le e))
      (pow_nonneg (R.family.S.a_pos m).le 4))
  have bill:=(price hr vv ww (fun i=>(paid₀ (vv i)).1) pay).filter_mono chosen
  let cut (N _:ℕ):Fin (N+1):=⟨N,Nat.lt_succ_self N⟩
  have limit:=profile_limit F L chosen cut φ hr age (a r) (b r)
  rw [(paid₀ α).1,(paid₀ (freeInput F J Z 4 r v)).1] at limit
  have ready:∀ᶠz:ℕ×ℕ in f.fuse,m<z.1:=by
    change ∀ᶠ_ :ℕ in atTop,∀ᶠ n:ℕ in atTop,m<f.mesh n
    exact .of_forall fun _=>f.mesh.cofinal.eventually_gt_atTop m
  filter_upwards [bill,ready.filter_mono (chosen.trans L.certified),
    Metric.tendsto_nhds.mp limit (ε/2*(g r)^q) (by positivity)] with z receipt live near
  refine ⟨live,?_⟩
  let fields:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
  let low:=earlier R (per:=z.2) live.le fields (dilate hr φ)
  let high:=profile R cut (fields 0) (fields 1) (dilate hr φ) z.1 z.2
  have identity:(fun i=>atRef L 4 r z (ww i))=fields:=by funext i;fin_cases i <;>rfl
  have logcost:=receipt live cut
  rw [identity,Fin.prod_univ_two] at logcost
  let t:=regulatorRun R.family z.1 z.2 m
  have tp:0≤t:=by dsimp only [t,regulatorRun];positivity
  have eligible:1/2<β m*(g r)^2:=by simpa only [m,level] using heat
  have boundt:t≤2*g r:=coupling_bound R simple le_rfl live.le gp eligible
  have Lp:0<Λ m:=by
    change 0<2+Real.log (β m)
    linarith only [Real.log_nonneg (R.family.path.levels.fits.delayed m).le]
  have first:‖low-high‖≤C*(Λ m^B)⁻¹+M*fee*(2*g r)^(2*(q+1)):=
    logcost.trans (cost mp Dp.le (norm_nonneg α) bound (by positivity) tp boundt fp q)
  have reduce:M*fee*(2*g r)^(2*(q+1))=(A*(g r)^(q+2))*(g r)^q:=by
    dsimp only [A];rw [mul_pow,show 2*(q+1)=(q+2)+q by omega,pow_add];ring
  have named:J r 4 (freeInput F J Z 4 r v)=homogeneous F J Z r 4 v:=rfl
  have raw:‖high-cov r‖≤ε/2*(g r)^q:=by
    change ‖profile R cut (atRef L 4 r z (a r)) (atRef L 4 r z (b r)) (dilate hr φ) z.1 z.2-
      tested (J r 4 α) (homogeneous F J Z r 4 v) r φ‖≤_
    simpa only [dist_eq_norm,named] using near.le
  have tri:‖low-cov r‖≤‖low-high‖+‖high-cov r‖:=by
    simpa only [dist_eq_norm] using dist_triangle low high (cov r)
  rw [reduce] at first
  have final:‖low-high‖≤C*(Λ m^B)⁻¹+ε/2*(g r)^q:=first.trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right small.le (pow_nonneg gp.le _)))
  exact tri.trans ((add_le_add final raw).trans_eq (by ring))

end YM.Integration.WilsonMatrixOriginalLogarithmicRate
