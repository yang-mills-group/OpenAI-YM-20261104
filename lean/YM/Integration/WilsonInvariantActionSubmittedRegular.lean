import YM.Integration.WilsonInvariantActionPromotedRegular
import YM.Integration.WilsonInvariantActionCalibratedColumn

/-! The regular-field estimate on a detected original action response, with the
same fixed compact Maxwell test, physical calibration, fields and mesh limits. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonInvariantActionSubmittedRegular
open Filter Function Set MeasureTheory Lattice Wilson RG RG17 Source Marker Extraction Extraction.Order
open Table Spec Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionIntegratedPair WilsonInvariantActionSpectatorPrices
open WilsonLimitConstruction
open scoped Classical Topology BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→tower S) (Z:WilsonPrescription G)
    {H:(Bel R.family.book).Hierarchy} (lead:Leading F J)
    (paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) (simple:G.Simple)
    {ρ:ℝ} {T:Campaign R} {P:Campaign.Pillars R T} (funded:FundedOriginalProperties.{u} simple ρ P)
    (pace:WilsonWindowReportingPace.Slow R.kit) (L:Layout F)
    {B:ℕ} (hB:0<B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    {U:Filter (ℕ×ℕ)} [U.NeBot] (chosen:U ≤ L.lens)
    {u₀:Filter (ℕ×ℕ)} (bank:Mantle F u₀) (E:Services R.family f S) (pegs:Pegs bank L)
local notation "β" => R.family.path.levels.clock.hatBeta

include lead paid simple funded pace hB level chosen E pegs in
theorem original (D:Profiles R 4)
    (sites:∀j:D.probes.index,∃w:(standard R.family.labels).Ref 4,
      D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 w)
    (K:ℝ) (decode:∀ᶠr in trail,∀y:S.Field 4,‖(homogeneous F J Z r 4).symm y‖ ≤ K*‖row F J Z D r y‖)
    {A:ℝ→Spin.change S 4} {δ g:ℝ→ℝ} (same:∀ᶠr in trail,J r 4=A r)
    (cent:∀ᶠr in trail,AlignV F.room.kernel F.sector H (A r)) (cal:TendC F A δ) (coupling:Coupling G g) :
    ∃ (j:D.probes.index) (v₀:(standard R.family.labels).Ref 4)
      (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀)
      (e:ℕ) (deposit:ℝ→RG17.Free R.family 4→R.family.label 4),
      let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
      let v:=(Bel R.family.book).project 4 v₀
      let b:=fun r=>homogeneous F J Z r 4 v
      let y:=fun r=>J r 4 (stepField R.family)
      let cov:=fun r=>WilsonInvariantActionPairCovariance.tested (y r) (b r) r φ
      let c:=tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
      c≠0 ∧ Tendsto cov trail (𝓝 c) ∧
      (∀(cut:(N p:ℕ)→Fin (N+1))(r:ℝ)(hr:0<r),f.limits
        (fun p=>suitable R.family.S p (dilate hr φ))
        (profile R cut (S.representative 4 (y r)) (S.representative 4 (b r)) (dilate hr φ)) (cov r)) ∧
      (∀ᶠr in trail,WilsonInvariantActionPairCovariance.tested (TraceExtension.center F) (b r) r φ≠0 ∧
        ((r^4/(4*δ r):ℝ):ℂ)=cov r / WilsonInvariantActionPairCovariance.tested (TraceExtension.center F) (b r) r φ) ∧
      (∀ᶠr in trail,∀u:RG17.Free R.family 4,master L 4 r (deposit r u)=J r 4 u ∧
        ∀N n,L.level r ≤ N→quota R.family 4 (L.level r) N n (atRef L 4 r (N,n) (deposit r u)) ≤
          R.family.S.a (L.level r)^4*(β (L.level r)^e*‖u‖)) ∧
      ∀q:ℕ,∀ε>0,∀ᶠr in trail,
      let s:=2*1+q+1+25;let k:=WilsonInvariantActionPosition.berth R s (L.level r)
      let ev:=(s+2)*5+e
      let a:=deposit r (stepField R.family);let w:=deposit r (freeInput F J Z 4 r v)
      master L 4 r a=y r ∧ master L 4 r w=b r ∧
      ∀(hr:0<r)(t:ℕ),t+1=k → ∀cut:(N p:ℕ)→Fin (N+1),
      ∀ᶠ z:ℕ×ℕ in U,∀live:t<z.1,
      let claim:=atRef L 4 r z a;let probe:=atRef L 4 r z w
      ‖WilsonInvariantActionPromotedPair.tested R (p:=z.2) live claim probe (dilate hr φ)-
        profile R cut (S.representative 4 (y r)) (S.representative 4 (b r)) (dilate hr φ) z.1 z.2‖ ≤ ε*(g r)^q ∧
      ∀η χ:ℂ→L[ℝ]ℝ,‖WilsonInvariantActionPromotedRegular.response R (per:=z.2) live claim probe
        (WilsonDegreeFourInheritedRange.height R (q+2*(ev+1)+2*ev) k) η χ (dilate hr φ)‖
        ≤ ε*(g r)^q*(‖η‖*‖χ‖) := by
  obtain ⟨j,v₀,hs,selection⟩:=WilsonInvariantActionCalibratedColumn.submitted F J Z lead paid simple D sites K decode same cent cal coupling
  have near:=WilsonMatrixTicketLanesReportedWindow.original R L simple pace hB level
  obtain ⟨e,deposit,market,comparison,_⟩:=WilsonFundedActionPairSector.original R simple funded F L chosen J lead paid bank E pegs near
  refine ⟨j,v₀,hs,e,deposit,?_⟩
  intro φ v b y cov c
  refine ⟨selection.1,selection.2.1,selection.2.2.1,selection.2.2.2,market,?_⟩
  intro q ε he
  let α:=stepField R.family
  let M:=‖α‖+‖v‖+2
  have hM : 0<M := by dsimp [M]; positivity
  have hα : ‖α‖ ≤ M := by dsimp [M]; linarith [norm_nonneg v]
  have hv : ‖v‖<M := by dsimp [M]; linarith [norm_nonneg α]
  have rent:∀ᶠr in trail,‖freeInput F J Z 4 r v‖ ≤ M :=
    (WilsonOriginalCompensatedAnchor.field F J Z lead paid simple 4 v).norm.eventually (ge_mem_nhds hv)
  let s:=2*1+q+1+25
  have geo:=WilsonInvariantActionPromotedPair.original R simple pace L hB level J lead paid coupling φ 1 q (ε:=ε/2) (by positivity)
  have sector:=WilsonInvariantActionPromotedRegular.filed R simple funded F L pace E hB level coupling s e q φ (ε:=ε/(M*M)) (by positivity)
  have grows:Tendsto L.level trail atTop:=by rw [level];exact WilsonMeasuredWindow.stop_tendsto _ simple B hB
  have warm:=(Next.Rank.Station.hat_rate R.family.path.levels simple).comp grows
  filter_upwards [market,comparison,geo,sector,rent,grows.eventually_ge_atTop (R.family.ref 4),
    warm.eventually_ge_atTop M,coupling.positive] with r bought prepared shift bill cap live large gp
  dsimp only
  let v':=freeInput F J Z 4 r v
  let a:=deposit r α;let w:=deposit r v'
  obtain ⟨ma,pa⟩:=bought α
  obtain ⟨mw,pw⟩:=bought v'
  refine ⟨ma,mw,?_⟩
  intro hr t date cut
  let k:=WilsonInvariantActionPosition.berth R s (L.level r)
  let roster:=Fin.cons (α:=fun _:Fin 2=>RG17.Free R.family 4) α (fun _=>v')
  let filed:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) a (fun _=>w)
  have norm (i:Fin 2) : ‖roster i‖ ≤ (β (L.level r))^1 := by
    rw [pow_one];fin_cases i
    · exact hα.trans large
    · exact cap.trans large
  have maps (i:Fin 2) : master L 4 r (filed i)=J r 4 (roster i) := by fin_cases i <;> assumption
  have drift:=prepared v' (dilate hr φ) cut
  have pin:∀ᶠ z:ℕ×ℕ in U,‖profile R cut (atRef L 4 r z a) (atRef L 4 r z w) (dilate hr φ) z.1 z.2 -
      profile R cut (S.representative 4 (y r)) (S.representative 4 (b r)) (dilate hr φ) z.1 z.2‖ ≤
      ε/2*(g r)^q := by
    filter_upwards [Metric.tendsto_nhds.mp drift (ε/2*(g r)^q) (by positivity)] with z hz
    rw [show b r=J r 4 v' by rfl,show y r=J r 4 α by rfl]
    simpa only [dist_zero_right,a,w,α] using hz.le
  filter_upwards [(shift hr roster filed norm live maps).filter_mono chosen,
    (bill hr t date live a w ‖α‖ ‖v'‖ (norm_nonneg _) (norm_nonneg _) pa pw).filter_mono chosen,pin]
    with z moved priced settled
  intro aged
  have hk:k ≤ z.1 := by dsimp only [k];rw [←date];exact aged
  constructor
  · have step:=moved hk cut
    have transport (d h:ℕ) (hd:d ≤ z.1) (hh:h ≤ z.1) (eq:d=h) :
        WilsonInvariantActionPromotedPair.tested R (p:=z.2) hd (atRef L 4 r z a) (atRef L 4 r z w) (dilate hr φ)=
        WilsonInvariantActionPromotedPair.tested R (p:=z.2) hh (atRef L 4 r z a) (atRef L 4 r z w) (dilate hr φ) := by
      cases eq; rfl
    have moved' : ‖WilsonInvariantActionPromotedPair.tested R (p:=z.2) aged (atRef L 4 r z a) (atRef L 4 r z w) (dilate hr φ) -
        profile R cut (atRef L 4 r z a) (atRef L 4 r z w) (dilate hr φ) z.1 z.2‖ ≤ ε/2*(g r)^q := by
      rw [transport (t+1) k aged hk date]; exact step
    let A:=WilsonInvariantActionPromotedPair.tested R (p:=z.2) aged (atRef L 4 r z a) (atRef L 4 r z w) (dilate hr φ)
    let B:=profile R cut (atRef L 4 r z a) (atRef L 4 r z w) (dilate hr φ) z.1 z.2
    let C:=profile R cut (S.representative 4 (y r)) (S.representative 4 (b r)) (dilate hr φ) z.1 z.2
    have tri : ‖A-C‖ ≤ ‖A-B‖+‖B-C‖ := by simpa only [dist_eq_norm] using dist_triangle A B C
    exact tri.trans ((add_le_add moved' settled).trans_eq (by ring))
  intro η χ
  have fee:=priced aged η χ
  have both : ‖α‖*‖v'‖ ≤ M*M := mul_le_mul hα cap (norm_nonneg _) hM.le
  calc
    _ ≤ (ε/(M*M))*(g r)^q*(‖η‖*‖χ‖)*(‖α‖*‖v'‖) := fee
    _ ≤ (ε/(M*M))*(g r)^q*(‖η‖*‖χ‖)*(M*M) := mul_le_mul_of_nonneg_left both (by positivity)
    _ = ε*(g r)^q*(‖η‖*‖χ‖) := by field_simp

end YM.Integration.WilsonInvariantActionSubmittedRegular
