import YM.Integration.WilsonInvariantActionCapturedProfile
import YM.Integration.WilsonInvariantActionLogarithmicGeometry

/-! Compare the original measured profile with its complete two earlier
registered regular fields on the manuscript's actual logarithmic mesh. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonInvariantActionLogarithmicReturn
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Extraction Extraction.Order Marker
open Spec RG17 Climb FullVolume Table OPE OPE.Therm PhysMS Trace.Pilot PhysicalNext.Repeat.Legato
open Next.UVStress RGComparison.Core16 WilsonLimitConstruction
open WilsonInvariantActionIntegratedPair WilsonInvariantActionPromotedPair
open WilsonInvariantActionCapturedCovariance WilsonInvariantActionCapturedPoints WilsonInvariantActionCapturedProfile
open private volume_bill row from YM.Integration.WilsonInvariantActionPromotedPair
open scoped Classical Topology BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book} (F:Spec.Final R.family f S)
    (L:Layout F) (J:ℝ→PhysMS.tower S) (lead:PhysMS.Leading F J) {H:(Bel R.family.book).Hierarchy}
    (paid:∀d:ℕ,∀ᶠr in trail,PhysMS.Frame.obedient F H (J r) d)
    (simple:G.Simple) {ρ:ℝ} {T:Campaign R} (W:Campaign.Pillars R T)
    (funded:FundedOriginalProperties.{u} simple ρ W) (subsidy:WilsonReportColumnSubsidy.Eligible R.kit)
    (pace:WilsonWindowReportingPace.Slow R.kit) {B:ℕ} (large:17 ≤ B)
    (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "Λ" => RG16.Lambda R.family.path.levels

include simple W funded subsidy J lead paid pace large level in
theorem filed (φ:Test 2):
    let mass:=(∫x,‖φ x‖)+1
    ∃ D:ℝ,0<D ∧ ∀e q:ℕ,∀ᶠr in trail,let m:=L.level r
      ∀(hr:0<r)(v:Fin 2→RG17.Free R.family 4)(w:Fin 2→R.family.label 4),
      (∀i,master L 4 r (w i)=J r 4 (v i)) →
      (∀i N p,m ≤ N →quota R.family 4 m N p (atRef L 4 r (N,p) (w i))≤R.family.S.a m^4*β m^e) →
      ∀ᶠ z:ℕ×ℕ in L.lens,∀live:m<z.1,∀cut:(N p:ℕ)→Fin (N+1),
      let marks:=fun i=>atRef L 4 r z (w i)
      ‖earlier R (per:=z.2) live.le marks (dilate hr φ)-profile R cut (marks 0) (marks 1) (dilate hr φ) z.1 z.2‖ ≤
      mass*((2+8*D*(∏i,‖v i‖))*(Λ m^B)⁻¹+
        WilsonReportSeparatedMoments.fee census both q*(Pert.Asymptotics.regulatorRun R.family z.1 z.2 m)^(2*q)):=by
  intro mass
  have hp:0<B:=by omega
  obtain ⟨D,a,Dp,ap,lipschitz⟩:=WilsonMovingReportDisplacement.purchased R simple L J lead paid
    (fun _:Fin 2=>4) (tsupport φ) φ.hasCompactSupport φ.tsupport_subset
  refine ⟨D,Dp,?_⟩
  intro e q
  have band:=WilsonInvariantActionLogarithmicGeometry.original R simple pace large φ
  rw [←level] at band
  have grows:Tendsto L.level trail atTop:=by rw [level];exact WilsonMeasuredWindow.stop_tendsto _ simple B hp
  have closepaid:=grows.eventually (WilsonInvariantActionCapturedPoints.at_date R simple W funded subsidy
    (br:=1) (by decide) 1 e q)
  have radius:=WilsonFundedMeasuredWindow.all_radii R pace simple hp
  have lograte:=Real.tendsto_log_atTop.comp ((Next.Rank.Station.hat_rate R.family.path.levels simple).comp grows)
  filter_upwards [band,lipschitz,closepaid,grows.eventually_ge_atTop (R.family.ref 4),
    (eventually_le_nhds (R.family.S.a_pos 0)).filter_mono nhdsWithin_le_nhds,
    lograte.eventually_ge_atTop (max 1 (8/a))] with r captured spatial transfer age tiny warm
  let m:=L.level r;let Z:=Λ m^B;let h:=Z⁻¹
  dsimp only
  intro hr v w master costs
  have loglo:1≤Real.log (β m):=(le_max_left ..).trans warm
  have l1:1≤Λ m:=by change 1≤2+Real.log (β m);linarith only [loglo]
  have zp:0<Z:=pow_pos (zero_lt_one.trans_le l1) _
  have log1:Λ m≤Z:=by simpa only [pow_one] using (pow_le_pow_right₀ l1 hp)
  have step:8*h≤a:=by
    have low:8/a≤Real.log (β m):=(le_max_right ..).trans warm
    have enough:8/a≤Z:=low.trans ((by change Real.log (β m)≤2+Real.log (β m);linarith : Real.log (β m)≤Λ m).trans log1)
    have pay:8≤a*Z:=by simpa only [mul_comm] using (div_le_iff₀ ap).mp enough
    simpa only [h,←div_eq_mul_inv] using (div_le_iff₀ zp).mpr pay
  have scaled:Λ m^B≤r/R.family.S.a m:=by simpa only [m,level] using (radius.2 r hr tiny).1
  have mesh:R.family.S.a m/r≤h:=by
    apply (div_le_iff₀ hr).mpr
    change R.family.S.a m≤Z⁻¹*r
    exact (le_inv_mul_iff₀ zp).mpr ((le_div_iff₀ (R.family.S.a_pos m)).mp scaled)
  let ψ:=dilate hr φ
  have total:=(WilsonExternalMeshMass.funded R.family f ψ ψ.continuous ψ.hasCompactSupport
    (show (0:ℝ)<1 by norm_num)).filter_mono L.certified
  have quote:=spatial hr v w (fun _=>age) master h (inv_pos.mpr zp)
  filter_upwards [total,quote] with z allocated localCost
  intro live cut
  let marks:=fun i=>atRef L 4 r z (w i)
  let c:=fun x:Fin 2→Site (R.family.side z.1 z.2)=>WilsonExternalMeshMass.charge R.family ψ x
  let old:=regularCov R (per:=z.2) live.le marks
  let high:=fun x:Fin 2→Site (R.family.side z.1 z.2)=>posterior R (someSlices R.family.path.levels z.2)
    (Nat.le_of_lt_succ (cut z.1 z.2).isLt) (marks 0) (marks 1) x
  let anchored:=fun x:Fin 2→Site (R.family.side z.1 z.2)=>posterior R (someSlices R.family.path.levels z.2)
    live.le (marks 0) (marks 1) (parents R live.le x)
  let C:=WilsonReportSeparatedMoments.fee census both q*(Pert.Asymptotics.regulatorRun R.family z.1 z.2 m)^(2*q)
  let E:=(2+8*D*(∏i,‖v i‖))*h+C
  have cp:0≤C:=mul_nonneg (WilsonReportSeparatedMoments.fee_nonneg census both q)
    (pow_nonneg (by unfold Pert.Asymptotics.regulatorRun;positivity) _)
  have ep:0≤E:=by dsimp only [E,h];positivity
  have billed (x):‖c x*(old x-high x)‖≤‖c x‖*E:=by
    by_cases hx:c x=0
    · simp only [hx,zero_mul,norm_zero,le_refl]
    let d:=WilsonInvariantActionSeparatedCells.gap R.family live.le x
    have geom:=captured hr z.1 z.2 live.le x hx
    have retained:=transfer d geom.1 (by simpa only [pow_one] using geom.2) z.1 z.2 live x
      (show d≤d∧d≤1*d by simp) marks (fun i=>costs i z.1 z.2 live.le)
    let z₀:=lift ∘ x
    let z₁:=WilsonReportCellProjection.ancestor (R.family.S.toDepth live.le z.2) ∘ z₀
    let X:=r⁻¹ • tag (R.family.S.a z.1) z₀
    let Y:=r⁻¹ • tag (R.family.S.a z.1) z₁
    have inside:X∈tsupport φ:=by
      apply subset_tsupport
      intro zero
      apply hx
      change (R.family.S.a z.1:ℂ)^(4*2)*((↑((r^(4*2))⁻¹):ℂ)*φ X)=0
      rw [zero,mul_zero,mul_zero]
    have near:‖Y-X‖≤8*h:=by
      have movement:=WilsonReportCellProjection.relative R.family.S live.le z.2 z₀ hr
      exact movement.trans (by change 4*(2:ℝ)*R.family.S.a m/r≤8*h;rw [mul_div_assoc];norm_num;gcongr)
    have xplot:tag (R.family.S.a z.1) z₀=r • X:=by simp [X,smul_smul,hr.ne']
    have yplot:tag (R.family.S.a z.1) z₁=r • Y:=by simp [Y,smul_smul,hr.ne']
    have placed:=localCost X inside Y (near.trans step) z₀ z₁ xplot yplot
    have compare:‖anchored x-high x‖≤(2+8*D*(∏i,‖v i‖))*h:=by
      change ‖posterior _ _ _ _ _ _-posterior _ _ _ _ _ _‖≤_
      rw [row R L r w live.le (age.trans live.le) cut x]
      refine placed.le.trans ?_
      calc
        _≤2*h+D*(∏i,‖v i‖)*(8*h):=by gcongr
        _=(2+8*D*(∏i,‖v i‖))*h:=by ring
    have capture:‖old x-anchored x‖≤C:=by rw [norm_sub_rev];exact retained
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_sub_le_norm_sub_add_norm_sub (old x) (anchored x) (high x)).trans
      ((add_le_add capture compare).trans_eq (add_comm ..))
  have amount:∑x,‖c x‖ ≤ mass:=by simpa only [c,ψ,volume_bill φ hr] using allocated
  have identity:earlier R (per:=z.2) live.le marks ψ-profile R cut (marks 0) (marks 1) ψ z.1 z.2=
      ∑x,c x*(old x-high x):=by
    simp only [earlier,profile,c,old,high,WilsonExternalMeshMass.charge,Finset.mul_sum,mul_sub,Finset.sum_sub_distrib,mul_assoc]
  rw [identity]
  exact (norm_sum_le ..).trans ((sum_le_sum fun x _=>billed x).trans ((sum_mul ..).symm.trans_le
    (mul_le_mul_of_nonneg_right amount ep)))

end YM.Integration.WilsonInvariantActionLogarithmicReturn
