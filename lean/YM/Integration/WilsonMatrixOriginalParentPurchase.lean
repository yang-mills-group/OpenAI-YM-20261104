import YM.Integration.WilsonMatrixOriginalMatchedForest

/-! The original nonzero signed panel and the finite retained forest on the same purchased labels. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixOriginalParentPurchase
open Filter Function Set Finset MeasureTheory Lattice Wilson RG Tree Precision RG17 Source Marker Extraction Spec
open FullVolume Table Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open Trace.Sundial WilsonInvariantActionSpectatorPrices WilsonLimitConstruction WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionCalibratedColumn WilsonMatrixOriginalEarlierPanel
open WilsonInvariantActionCapturedProfile WilsonMatrixOriginalReportingMargin
open private component from YM.Integration.WilsonMatrixOriginalEarlierPanel
open scoped Classical BigOperators Topology

variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S)
    (J:ℝ→tower S) (Z:WilsonPrescription G) {H:(Bel R.family.book).Hierarchy}
    (L:Layout F) {U:Filter (ℕ×ℕ)}
local notation "β" => R.family.path.levels.clock.hatBeta

def Detected (g:ℝ→ℝ) (a b:ℝ→R.family.label 4) (φ:Test 2) (c:ℂ) (χ:ℂ→L[ℝ]ℝ) (σ:ℝ):Prop:=
  ∀q:ℕ,∀ε>0,∀ᶠr in trail,let m:=L.level r
    ∀hr:0<r,∀ᶠz:ℕ×ℕ in U,∃live:m<z.1,
    let w:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
    let high:=WilsonInvariantActionPromotedPair.tested R (p:=z.2) live.le (w 0) (w 1) (dilate hr φ)
    let low:=earlier R (per:=z.2) live.le w (dilate hr φ)
    ‖high-low‖≤ε*(g r)^q ∧ |χ c|/4<σ*χ high

def ForestRow (δ g:ℝ→ℝ) : Prop :=
  ∃(D:Profiles R 4)(j:D.probes.index)(v₀:(standard R.family.labels).Ref 4)
    (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀)
    (e:ℕ)(deposit:ℝ→RG17.Free R.family 4→R.family.label 4)(χ:ℂ→L[ℝ]ℝ)(σ:ℝ),
    let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
    let v:=(Bel R.family.book).project 4 v₀
    let a:=fun r=>deposit r (stepField R.family)
    let b:=fun r=>deposit r (freeInput F J Z 4 r v)
    let c:=tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
    Row (H:=H) (U:=U) F J Z L δ g D j v₀ hs e deposit χ σ ∧
    LeadingRow (U:=U) F L a b φ c χ σ ∧ Detected (U:=U) F L g a b φ c χ σ ∧
    WilsonMatrixOriginalMatchedForest.Signed (U:=U) F L (e+1) g a b φ

private def Covered (e:ℕ) (a b:ℝ→R.family.label 4):Prop:=
  ∀ᶠr in trail,∀i:Fin 2,∀N p,L.level r≤N→quota R.family 4 (L.level r) N p
    (atRef L 4 r (N,p) ((Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (a r) (fun _=>b r)) i))≤
    R.family.S.a (L.level r)^4*β (L.level r)^e

private theorem at_inputs (lead:Leading F J) (paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (simple:G.Simple) {B:ℕ} (pos:0<B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    (e:ℕ) (deposit:ℝ→RG17.Free R.family 4→R.family.label 4) (v:RG17.Free R.family 4)
    (market:∀ᶠr in trail,∀w:RG17.Free R.family 4,master L 4 r (deposit r w)=J r 4 w ∧
      ∀N p,L.level r≤N→quota R.family 4 (L.level r) N p (atRef L 4 r (N,p) (deposit r w))≤
        R.family.S.a (L.level r)^4*(β (L.level r)^e*‖w‖)):
    Covered F L (e+1) (fun r=>deposit r (stepField R.family)) (fun r=>deposit r (freeInput F J Z 4 r v)):=by
  let α:=stepField R.family
  let a:=fun r=>deposit r α
  let b:=fun r=>deposit r (freeInput F J Z 4 r v)
  let K:=‖α‖+‖v‖+2
  have hα:‖α‖≤K:=by dsimp only [K];linarith [norm_nonneg v]
  have hv:‖v‖<K:=by dsimp only [K];linarith [norm_nonneg α]
  have bounded:∀ᶠr in trail,‖freeInput F J Z 4 r v‖≤K:=
    (WilsonOriginalCompensatedAnchor.field F J Z lead paid simple 4 v).norm.eventually (ge_mem_nhds hv)
  have grow:Tendsto L.level trail atTop:=by rw [level];exact WilsonMeasuredWindow.stop_tendsto _ simple B pos
  let tags:=fun r=>Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (a r) (fun _=>b r)
  have cover:∀ᶠr in trail,∀i:Fin 2,∀N p,L.level r≤N→
      quota R.family 4 (L.level r) N p (atRef L 4 r (N,p) (tags r i))≤
        R.family.S.a (L.level r)^4*β (L.level r)^(e+1):=by
    filter_upwards [market,bounded,((Next.Rank.Station.hat_rate R.family.path.levels simple).comp grow).eventually_ge_atTop K]
      with r sale bound warm i N p later
    let m:=L.level r
    have unit (t:RG17.Free R.family 4) (size:‖t‖≤β m):
        quota R.family 4 m N p (atRef L 4 r (N,p) (deposit r t))≤R.family.S.a m^4*β m^(e+1):=by
      rw [pow_succ]
      exact ((sale t).2 N p later).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left size
        (pow_nonneg (zero_lt_one.trans (R.family.path.levels.fits.delayed m)).le e)) (pow_nonneg (R.family.S.a_pos m).le 4))
    fin_cases i
    · exact unit α (hα.trans warm)
    · exact unit _ (bound.trans warm)
  exact cover

private theorem on_two {X Y:Type*} (f:X→Y) (x y:X) (i:Fin 2):
    Fin.cons (α:=fun _:Fin 2=>Y) (f x) (fun _=>f y) i=f (Fin.cons (α:=fun _:Fin 2=>X) x (fun _=>y) i):=by
  fin_cases i <;> rfl

private theorem detect (simple:G.Simple) {ρ:ℝ} {T:Campaign R} (W:Campaign.Pillars R T)
    (funded:FundedOriginalProperties.{u} simple ρ W) (subsidy:WilsonReportColumnSubsidy.Eligible R.kit)
    (pace:WilsonWindowReportingPace.Slow R.kit) {B:ℕ} (large:17≤B)
    (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B) (chosen:U≤L.lens)
    {g:ℝ→ℝ} (coupling:Coupling G g) (e:ℕ)
    (a b:ℝ→R.family.label 4) (φ:Test 2) (c:ℂ) (χ:ℂ→L[ℝ]ℝ) (σ:ℝ)
    (polar:χ=Complex.reCLM∨χ=Complex.imCLM) (sgn:σ=1∨σ= -1) (positive:0 < |χ c|)
    (lower:LeadingRow (U:=U) F L a b φ c χ σ) (cover:Covered F L e a b):
    Detected (U:=U) F L g a b φ c χ σ:=by
  intro q ε ep
  have none:0 < |χ c|/8:=by positivity
  let invoice:=WilsonMatrixOriginalMatchedSites.filed R F L simple W funded subsidy pace large level chosen coupling e
  filter_upwards [invoice q φ ep,invoice 0 φ none,lower 1 one_pos,cover] with r exactPrice extra sign credit
  intro m hr
  filter_upwards [exactPrice hr,extra hr,sign hr] with z estimate fixed hl
  obtain ⟨live,_,margin⟩:=hl
  let w:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
  let high:=WilsonInvariantActionPromotedPair.tested R (p:=z.2) live.le (w 0) (w 1) (dilate hr φ)
  let low:=earlier R (per:=z.2) live.le w (dilate hr φ)
  have bill i:quota R.family 4 m z.1 z.2 (w i)≤R.family.S.a m^4*β m^e:=by
    dsimp only [w];rw [on_two];exact credit i z.1 z.2 live.le
  refine ⟨live,estimate live w bill,?_⟩
  have gap:|χ high-χ low|≤|χ c|/8:=by
    apply (component χ polar high low).trans
    simpa only [pow_zero,mul_one] using fixed live w bill
  change |χ c|/2<σ*χ low at margin
  change |χ c|/4<σ*χ high
  obtain ⟨g₁,g₂⟩:=abs_le.mp gap
  rcases sgn with rfl|rfl <;> simp only [one_mul,neg_one_mul] at * <;> linarith

theorem booked (lead:Leading F J) (paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (simple:G.Simple) {ρ:ℝ} {T:Campaign R} (W:Campaign.Pillars R T)
    (funded:FundedOriginalProperties.{u} simple ρ W) (subsidy:WilsonReportColumnSubsidy.Eligible R.kit)
    (fund:WilsonMatrixTicketLanesReportedPrepaid.Paid G R.kit) (pace:WilsonWindowReportingPace.Slow R.kit)
    {B:ℕ} (large:17≤B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    (chosen:U≤L.lens) {δ g:ℝ→ℝ} (coupling:Coupling G g)
    (original:Measured (H:=H) (U:=U) F J Z L B δ g):ForestRow (H:=H) (U:=U) F J Z L δ g:=by
  obtain ⟨D,j,v₀,hs,e,deposit,χ,σ,row,_,lower⟩:=original
  let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
  let α:=stepField R.family
  let v:=(Bel R.family.book).project 4 v₀
  let a:=fun r=>deposit r α
  let b:=fun r=>deposit r (freeInput F J Z 4 r v)
  let c:=tree (D.probes.shell j) (test D j) H 4 α
  refine ⟨D,j,v₀,hs,e,deposit,χ,σ,row,lower,?_⟩
  obtain ⟨polar,sgn,_,positive,_,_,_,market,_⟩:=row
  have cover:=at_inputs F J Z L lead paid simple (by omega : 0<B) level e deposit v market
  exact ⟨detect F L simple W funded subsidy pace large level chosen coupling (e+1) a b φ c χ σ
      polar sgn positive lower cover,
    WilsonMatrixOriginalMatchedForest.filed F L simple fund pace (by omega) level chosen coupling (e+1) a b φ cover⟩

theorem on_run (simple:G.Simple) {ρ:ℝ} {T:Campaign R} (W:Campaign.Pillars R T)
    (funded:FundedOriginalProperties.{u} simple ρ W) (subsidy:WilsonReportColumnSubsidy.Eligible R.kit)
    (fund:WilsonMatrixTicketLanesReportedPrepaid.Paid G R.kit) (pace:WilsonWindowReportingPace.Slow R.kit)
    (Z:WilsonPrescription G) {B:ℕ} (large:17≤B) (v:Extraction.Order):
    ∃(w:Extraction.Order)(S:Table R.family.book)(F:Final R.family (v.refine w) S)
      (H:(Bel R.family.book).Hierarchy)(J:ℝ→tower S)(A:ℝ→Spin.change S 4)(δ:ℝ→ℝ)(L:Layout F),
      Leading F J ∧ (∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) ∧
      (∀ᶠr in trail,J r 4=A r) ∧ TendC F A δ ∧ Coupling G (glo A) ∧
      L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B ∧ L.lens≤(v.refine w).fuse ∧
      ForestRow (H:=H) (U:=L.lens) F J Z L δ (glo A):=by
  obtain ⟨w,S,F,H,J,A,δ,L,lead,paid,same,cal,coupling,level,lens,measured⟩:=
    WilsonMatrixOriginalReportingMargin.on_run simple W funded subsidy pace Z large v
  exact ⟨w,S,F,H,J,A,δ,L,lead,paid,same,cal,coupling,level,lens,
    booked F J Z L lead paid simple W funded subsidy fund pace large level le_rfl coupling measured⟩

end YM.Integration.WilsonMatrixOriginalParentPurchase
