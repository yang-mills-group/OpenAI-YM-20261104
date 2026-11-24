import YM.Integration.WilsonMatrixOriginalLogarithmicRate
import YM.Integration.WilsonMatrixOriginalFundedEarlierPanel

/-! The nonzero signed free two-site value is attained on the original, order-independent reporting clock. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixOriginalReportingMargin
open Filter Function Set MeasureTheory Lattice Wilson RG RG17 Source Marker Extraction Extraction.Order
open Table Spec Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionSpectatorPrices WilsonInvariantActionPairCovariance
open WilsonInvariantActionCalibratedColumn WilsonInvariantActionPosition WilsonInvariantActionCapturedProfile
open Trace.Sundial WilsonLimitConstruction WilsonMatrixOriginalEarlierPanel WilsonMatrixOriginalLogarithmicRate
open private component from YM.Integration.WilsonMatrixOriginalEarlierPanel
open scoped Classical Topology BigOperators

variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S)
  (J:ℝ→tower S) (Z:WilsonPrescription G) {H:(Bel R.family.book).Hierarchy}
  (L:Layout F) {U:Filter (ℕ×ℕ)} [U.NeBot]
local notation "Λ" => RG16.Lambda R.family.path.levels

def LeadingRow (a b:ℝ→R.family.label 4) (φ:Test 2) (c:ℂ) (χ:ℂ→L[ℝ]ℝ) (σ:ℝ) : Prop :=
  ∀ε>0,∀ᶠr in trail,let m:=L.level r
    ∀hr:0<r,∀ᶠz:ℕ×ℕ in U,∃live:m<z.1,
    let marks:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
    let low:=earlier R (per:=z.2) live.le marks (dilate hr φ)
    ‖low-c‖≤ε ∧ |χ c|/2<σ*χ low

omit [U.NeBot] in
theorem from_rate (simple:G.Simple) {B:ℕ} (hp:0<B)
    (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    (g:ℝ→ℝ) (a b:ℝ→R.family.label 4) (φ:Test 2) (cov:ℝ→ℂ) (c:ℂ)
    (χ:ℂ→L[ℝ]ℝ) (σ:ℝ) (polar:χ=Complex.reCLM∨χ=Complex.imCLM)
    (sgn:σ=1∨σ= -1) (positive:0< |χ c|) (oriented:σ*χ c=|χ c|)
    (seen:Tendsto cov trail (𝓝 c)) (rate:Rate (U:=U) F L B g a b φ cov):
    LeadingRow (U:=U) F L a b φ c χ σ := by
  obtain ⟨C,_Cp,priced⟩:=rate
  have grows:Tendsto L.level trail atTop:=by rw [level];exact WilsonMeasuredWindow.stop_tendsto _ simple B hp
  have zoom: Tendsto (fun r=>(Λ (L.level r)^B)⁻¹) trail (𝓝 0):=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop hp.ne').comp ((RG16.Literal.lambda_leads R.family simple).comp grows))
  have shrink:Tendsto (fun r=>C*(Λ (L.level r)^B)⁻¹) trail (𝓝 0):=by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=C)).mul zoom
  intro ε ep
  let η:=min (ε/3) (|χ c|/8)
  have pay:0<η:=lt_min (by linarith) (by linarith)
  have near:∀ᶠr in trail,‖cov r-c‖<η:=by
    simpa only [dist_eq_norm] using Metric.tendsto_nhds.mp seen η pay
  filter_upwards [priced 0 η pay,shrink.eventually (gt_mem_nhds pay),near] with r promise fee hit
  intro m hr
  filter_upwards [promise hr] with z received
  obtain ⟨live,cost⟩:=received
  let marks:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (atRef L 4 r z (a r)) (fun _=>atRef L 4 r z (b r))
  let low:=earlier R (per:=z.2) live.le marks (dilate hr φ)
  have old:‖low-cov r‖≤C*(Λ m^B)⁻¹+η:=by simpa only [pow_zero,mul_one] using cost
  have tri:‖low-c‖≤‖low-cov r‖+‖cov r-c‖:=by simpa only [dist_eq_norm] using dist_triangle low (cov r) c
  have bound:‖low-c‖≤3*η:=by linarith only [tri,old,fee,hit]
  have small:|χ low-χ c|≤3*η:=(component χ polar low c).trans bound
  obtain ⟨left,right⟩:=abs_le.mp small
  have up:η≤ε/3:=min_le_left _ _
  have down:η≤|χ c|/8:=min_le_right _ _
  refine ⟨live,by linarith only [bound,up],?_⟩
  rcases sgn with rfl | rfl <;> simp only [one_mul,neg_one_mul] at * <;>
    linarith only [left,right,positive,oriented,down]

def Measured (B:ℕ) (δ g:ℝ→ℝ) : Prop :=
  ∃ (D:Profiles R 4) (j:D.probes.index) (v₀:(standard R.family.labels).Ref 4)
    (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀)
    (e:ℕ) (deposit:ℝ→RG17.Free R.family 4→R.family.label 4) (χ:ℂ→L[ℝ]ℝ) (σ:ℝ),
    let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
    let v:=(Bel R.family.book).project 4 v₀
    let a:=fun r=>deposit r (stepField R.family)
    let b:=fun r=>deposit r (freeInput F J Z 4 r v)
    let cov:=fun r=>tested (J r 4 (stepField R.family)) (homogeneous F J Z r 4 v) r φ
    let c:=tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
    Row (H:=H) (U:=U) F J Z L δ g D j v₀ hs e deposit χ σ ∧
      Rate (U:=U) F L B g a b φ cov ∧ LeadingRow (U:=U) F L a b φ c χ σ

theorem captured (lead:Leading F J) (paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (simple:G.Simple) {ρ:ℝ} {T:Campaign R} (W:Campaign.Pillars R T)
    (funded:FundedOriginalProperties.{u} simple ρ W)
    (subsidy:WilsonReportColumnSubsidy.Eligible R.kit) (pace:WilsonWindowReportingPace.Slow R.kit)
    {B:ℕ} (large:17≤B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    (chosen:U≤L.lens) {δ g:ℝ→ℝ} (coupling:Coupling G g)
    (prior:Captured (H:=H) (U:=U) F J Z L δ g):Measured (H:=H) (U:=U) F J Z L B δ g:=by
  obtain ⟨D,j,v₀,hs,e,deposit,χ,σ,record⟩:=prior
  have original:=record
  obtain ⟨polar,sgn,orient,gain,seen,_⟩:=original
  have price:=WilsonMatrixOriginalLogarithmicRate.filed F J Z L chosen lead paid simple W funded subsidy
    pace large level coupling D j v₀ hs e deposit χ σ record
  exact ⟨D,j,v₀,hs,e,deposit,χ,σ,record,price,
    from_rate F L simple (by omega) level g _ _ _ _ _ χ σ polar sgn gain orient seen price⟩

theorem on_run (simple:G.Simple) {ρ:ℝ} {T:Campaign R} (W:Campaign.Pillars R T)
    (funded:FundedOriginalProperties.{u} simple ρ W) (subsidy:WilsonReportColumnSubsidy.Eligible R.kit)
    (pace:WilsonWindowReportingPace.Slow R.kit) (N:WilsonPrescription G) {B:ℕ}
    (large:17≤B) (v:Extraction.Order):
    ∃(w:Extraction.Order)(S:Table R.family.book)(F:Final R.family (v.refine w) S)
      (H:(Bel R.family.book).Hierarchy)(J:ℝ→tower S)(A:ℝ→Spin.change S 4)(δ:ℝ→ℝ)(L:Layout F),
      Leading F J ∧ (∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) ∧
      (∀ᶠr in trail,J r 4=A r) ∧ TendC F A δ ∧ Coupling G (glo A) ∧
      L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B ∧ L.lens≤(v.refine w).fuse ∧
      Measured (H:=H) (U:=L.lens) F J N L B δ (glo A):=by
  obtain ⟨w,S,F,H,_,_,J,A,δ,_,_,L,_,lead,paid,same,_,cal,coupling,_,level,lens,prior⟩:=
    WilsonMatrixOriginalFundedEarlierPanel.on_run simple W funded subsidy pace N (B:=B) (by omega) v
  letI : L.lens.NeBot := L.notbot
  exact ⟨w,S,F,H,J,A,δ,L,lead,paid,same,cal,coupling,level,lens,
    captured F J N L lead paid simple W funded subsidy pace large level le_rfl coupling prior⟩

end YM.Integration.WilsonMatrixOriginalReportingMargin
