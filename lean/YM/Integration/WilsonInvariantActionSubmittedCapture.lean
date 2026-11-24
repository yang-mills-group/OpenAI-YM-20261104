import YM.Integration.WilsonInvariantActionCapturedProfile
import YM.Integration.WilsonInvariantActionSubmittedRegular

/-! On a detected, calibrated physical action column, the signed integral of
the two complete earlier regular fields already gives the full physical
response, with any requested measured-coupling accuracy. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonInvariantActionSubmittedCapture
open Filter Function Set MeasureTheory Lattice Wilson RG RG17 Source Marker Extraction Extraction.Order
open Table Spec Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionIntegratedPair WilsonInvariantActionSpectatorPrices
open WilsonInvariantActionPosition WilsonInvariantActionCapturedProfile
open WilsonLimitConstruction
open scoped Classical Topology BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→tower S) (Z:WilsonPrescription G)
    {H:(Bel R.family.book).Hierarchy} (lead:Leading F J)
    (paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) (simple:G.Simple)
    {ρ:ℝ} {T:Campaign R} {P:Campaign.Pillars R T} (funded:FundedOriginalProperties.{u} simple ρ P)
    (subsidy:WilsonReportColumnSubsidy.Eligible R.kit)
    (pace:WilsonWindowReportingPace.Slow R.kit) (L:Layout F)
    {B:ℕ} (hB:0<B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    {U:Filter (ℕ×ℕ)} [U.NeBot] (chosen:U ≤ L.lens)
    {u₀:Filter (ℕ×ℕ)} (bank:Mantle F u₀) (E:Services R.family f S) (pegs:Pegs bank L)
local notation "β" => R.family.path.levels.clock.hatBeta

private theorem atDate {l k N per:ℕ} (d:l=k) (hl:l≤N) (hk:k≤N) (a b:R.family.label 4) (φ:Test 2):
    WilsonInvariantActionPromotedPair.tested R (p:=per) hl a b φ=WilsonInvariantActionPromotedPair.tested R (p:=per) hk a b φ:=by cases d;rfl

include lead paid simple funded subsidy pace hB level chosen E pegs in
theorem original (D:Profiles R 4)
    (sites:∀j:D.probes.index,∃w:(standard R.family.labels).Ref 4,
      D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 w)
    (K:ℝ) (decode:∀ᶠr in trail,∀y:S.Field 4,‖(homogeneous F J Z r 4).symm y‖ ≤ K*‖row F J Z D r y‖)
    {A:ℝ→Spin.change S 4} {δ g:ℝ→ℝ} (same:∀ᶠr in trail,J r 4=A r)
    (cent:∀ᶠr in trail,AlignV F.room.kernel F.sector H (A r)) (cal:TendC F A δ) (coupling:Coupling G g):
    ∃(j:D.probes.index)(v₀:(standard R.family.labels).Ref 4)
      (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀)
      (e:ℕ)(deposit:ℝ→RG17.Free R.family 4→R.family.label 4),
      let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
      let v:=(Bel R.family.book).project 4 v₀
      let b:=fun r=>homogeneous F J Z r 4 v
      let y:=fun r=>J r 4 (stepField R.family)
      let cov:=fun r=>WilsonInvariantActionPairCovariance.tested (y r) (b r) r φ
      let c:=tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
      c≠0 ∧ Tendsto cov trail (𝓝 c) ∧
      (∀ᶠr in trail,WilsonInvariantActionPairCovariance.tested (TraceExtension.center F) (b r) r φ≠0 ∧
        ((r^4/(4*δ r):ℝ):ℂ)=cov r / WilsonInvariantActionPairCovariance.tested (TraceExtension.center F) (b r) r φ) ∧
      (∀ᶠr in trail,∀u:RG17.Free R.family 4,master L 4 r (deposit r u)=J r 4 u ∧
        ∀N n,L.level r≤N→quota R.family 4 (L.level r) N n (atRef L 4 r (N,n) (deposit r u))≤
          R.family.S.a (L.level r)^4*(β (L.level r)^e*‖u‖)) ∧
      ∀q:ℕ,∀ε>0,∀ᶠr in trail,let k:=berth R (2*1+q+1+25) (L.level r)
        let a:=deposit r (stepField R.family);let w:=deposit r (freeInput F J Z 4 r v)
        master L 4 r a=y r ∧ master L 4 r w=b r ∧
        ∀hr:0<r,∀ᶠz:ℕ×ℕ in U,∃live:k<z.1,
        let marks:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z a) (fun _=>atRef L 4 r z w)
        ‖earlier R (per:=z.2) live.le marks (dilate hr φ)-cov r‖≤ε*(g r)^q:=by
  obtain ⟨j,v₀,hs,e,deposit,gained⟩:=WilsonInvariantActionSubmittedRegular.original F J Z lead paid simple funded pace L hB level chosen bank E pegs D sites K decode same cent cal coupling
  refine ⟨j,v₀,hs,e,deposit,?_⟩
  intro φ v b y cov c
  obtain ⟨nc,sees,limits,ward,market,sources⟩:=gained
  refine ⟨nc,sees,ward,market,?_⟩
  intro q ε he
  let α:=stepField R.family;let M:=‖α‖+‖v‖+2
  have hα:‖α‖≤M:=by dsimp only [M];linarith [norm_nonneg v]
  have hv:‖v‖<M:=by dsimp only [M];linarith [norm_nonneg α]
  have rent:∀ᶠr in trail,‖freeInput F J Z 4 r v‖≤M:=
    (WilsonOriginalCompensatedAnchor.field F J Z lead paid simple 4 v).norm.eventually (ge_mem_nhds hv)
  let s:=2*1+q+1+25
  have saved:=sources q (ε/3) (by positivity)
  have captured:=WilsonInvariantActionCapturedProfile.filed R F L simple P funded subsidy pace E
    hB level coupling (s:=s) (by dsimp only [s];omega) (e+1) q φ (ε:=ε/3) (by positivity)
  have grows:Tendsto L.level trail atTop:=by rw [level];exact WilsonMeasuredWindow.stop_tendsto _ simple B hB
  have warm:=(Next.Rank.Station.hat_rate R.family.path.levels simple).comp grows
  filter_upwards [market,saved,captured,rent,grows.eventually_ge_atTop (R.family.ref 4),
    warm.eventually_ge_atTop M,coupling.positive] with r paid0 snapshot reduce cap ref large gp
  let m:=L.level r;let k:=berth R s m
  let v':=freeInput F J Z 4 r v
  let a:=deposit r α;let w:=deposit r v'
  let submitted:Fin 2→R.family.label 4:=Fin.cons a (fun _=>w)
  have fundedMarks (i:Fin 2) (N p:ℕ) (age:m≤N):
      quota R.family 4 m N p (atRef L 4 r (N,p) (submitted i))≤R.family.S.a m^4*β m^(e+1):=by
    have upper (u:RG17.Free R.family 4) (size:‖u‖≤β m):
        quota R.family 4 m N p (atRef L 4 r (N,p) (deposit r u))≤R.family.S.a m^4*β m^(e+1):=by
      rw [pow_succ (β m)]
      exact ((paid0 u).2 N p age).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left size
        (pow_nonneg ((norm_nonneg u).trans size) e)) (pow_nonneg (R.family.S.a_pos m).le 4))
    fin_cases i
    · exact upper α (hα.trans large)
    · exact upper v' (cap.trans large)
  refine ⟨snapshot.1,snapshot.2.1,?_⟩
  intro hr
  let cut (N _:ℕ):Fin (N+1):=⟨N,Nat.lt_succ_self N⟩
  let t:=k-1
  have hk:1≤k:=(Nat.succ_le_succ (Nat.zero_le m)).trans (arrival R s m).1
  have dt:t+1=k:=Nat.sub_add_cancel hk
  have moving:=snapshot.2.2 hr t dt cut
  have quoted:=(reduce hr ref submitted fundedMarks).filter_mono chosen
  have limit:=(along (limits cut r hr)).mono_left (chosen.trans L.certified)
  have early:∀ᶠz:ℕ×ℕ in f.fuse,k<z.1:=by
    change ∀ᶠ_ :ℕ in atTop,∀ᶠ n:ℕ in atTop,k<f.mesh n
    exact .of_forall fun _=>f.mesh.cofinal.eventually_gt_atTop k
  filter_upwards [moving,quoted,(Metric.tendsto_nhds.mp limit (ε/3*(g r)^q) (by positivity)),
    early.filter_mono (chosen.trans L.certified)] with z moved received near live
  refine ⟨live,?_⟩
  let z₀:=atRef L 4 r z a;let z₁:=atRef L 4 r z w
  let marks:Fin 2→R.family.label 4:=Fin.cons z₀ (fun _=>z₁)
  have sameMarks:(fun i=>atRef L 4 r z (submitted i))=marks:=by funext i;fin_cases i <;>rfl
  rw [sameMarks] at received
  have ht:t<z.1:=by rw [show t<z.1 ↔ t+1≤z.1 by omega,dt];exact live.le
  have shift:=(moved ht).1
  rw [atDate dt ht live.le] at shift
  let old:=earlier R (per:=z.2) live.le marks (dilate hr φ)
  let full:=WilsonInvariantActionPromotedPair.tested R (p:=z.2) live.le z₀ z₁ (dilate hr φ)
  let upper:=profile R cut (S.representative 4 (y r)) (S.representative 4 (b r)) (dilate hr φ) z.1 z.2
  have r0:‖old-full‖≤ε/3*(g r)^q:=by rw [norm_sub_rev];exact received live
  have r1:‖full-upper‖≤ε/3*(g r)^q:=shift
  have r2:‖upper-cov r‖≤ε/3*(g r)^q:=by simpa only [dist_eq_norm] using near.le
  have tri (o a b:ℂ):‖o-b‖≤‖o-a‖+‖a-b‖:=by simpa only [dist_eq_norm] using dist_triangle o a b
  exact (tri old full (cov r)).trans ((add_le_add r0 ((tri full upper (cov r)).trans
    (add_le_add r1 r2))).trans_eq (by ring))

end YM.Integration.WilsonInvariantActionSubmittedCapture
