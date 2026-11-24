import YM.Integration.WilsonMatrixOriginalGermSlabBudget
import YM.Integration.WilsonMatrixOriginalGermSelectedSpring
import YM.Integration.WilsonMatrixOriginalParentPurchase

/-! The selected nonzero two-site Ward observation on its original signed
test pays the spring-mask substitution at every period, across an
unbounded number of genuine ultraviolet stages. Both proper means use
the same original Wilson law as the two-field joint. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermSlabHearing
open IterationFour IterationFour.Vacuum Comparison.RG02
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato Work.F03 Bid
open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoherentMayerHearing Dict06.Series
open Census Window
open Bloch Laurent RG.Supply Extra.Histories GapsLocal.Renew PhysicalNext.Repeat.Opera
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Bloom WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Fk
open scoped BigOperators Classical ENNReal
open Filter Function Set Finset MeasureTheory Lattice Wilson RG Tree Precision RG17 Source Marker Extraction Extraction.Order Spec
open Table Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm Next.UVStress
open PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register Pert.Asymptotics
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionSpectatorPrices WilsonInvariantActionCalibratedColumn
open Trace.Sundial WilsonLimitConstruction WilsonMatrixOriginalEarlierPanel WilsonInvariantActionPairCovariance
open WilsonMatrixTicketLanesRegulatorColumn WilsonMatrixTicketLanesRegisteredCovariance
open OriginalMarkedRunAction
open scoped Classical Topology BigOperators
open WilsonMatrixOriginalGermPanelRMS WilsonMatrixOriginalGermConditionalMask
open private coupling_bound from YM.Integration.WilsonInvariantActionPromotedRegular
open private Covered at_inputs from YM.Integration.WilsonMatrixOriginalParentPurchase
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→tower S) (Z₀:WilsonPrescription G) (L:Layout F)
    {H:(Bel R.family.book).Hierarchy} {U:Filter (ℕ×ℕ)}

def Billed (R:Run G) (j N:ℕ) (live:j≤N) (Z:SeriesA G) (σ C:ℝ) (load:ℕ)
    (marks:ℕ→Fin 2→R.family.label 4) (φ:Test 2) (income:ℝ):Prop:=
  ∀p (x:Site (R.family.side j p)),
    let t:=regulatorRun R.family N p j
    let S:=fun V=>springAt R N p j load Z t x V
    let M:=fun V=>maskedSpringAt R N p j load Z σ C t x V
    let W:=fun V=>((M V-S V:ℝ):ℂ)
    let amount:=bill R (le_refl j) live W (marks p) φ
    HasDerivAt (fun s=>hearing R (le_refl j) live (fun V=>((-S V:ℝ):ℂ)) (marks p) φ s-
      hearing R (le_refl j) live (fun V=>((-M V:ℝ):ℂ)) (marks p) φ s) amount 0 ∧
      amount=(∫V,response R (le_refl j) live (marks p) φ V*W V ∂scene R.family.path N p j) ∧
      ‖amount‖ ≤ income

private theorem spend {j N:ℕ} (live:j≤N) {Z:SeriesA G} {σ C amount income:ℝ} {load:ℕ}
    (sold:WilsonMatrixOriginalGermSelectedSpring.Signed R j N live Z σ C load amount)
    (marks:ℕ→Fin 2→R.family.label 4) (φ:Test 2)
    (cash:∀p,cost R (p:=p) (le_refl j) live (marks p) φ*amount≤ income):
    Billed R j N live Z σ C load marks φ income:=by
  intro p x
  obtain ⟨der,read,norm⟩:=sold p x j le_rfl (marks p) φ
  exact ⟨der,read,norm.trans (cash p)⟩

theorem on_row (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
    {B:ℕ} (wide:17≤B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    (lead:Leading F J) (obey:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    {g δ₀:ℝ→ℝ} (coupling:Coupling G g) {D:Profiles R 4} {j:D.probes.index}
    {v₀:(standard R.family.labels).Ref 4} {hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀}
    {e₀:ℕ} {deposit:ℝ→RG17.Free R.family 4→R.family.label 4} {χ:ℂ→L[ℝ]ℝ} {sign:ℝ}
    (row:Row (H:=H) (U:=U) F J Z₀ L δ₀ g D j v₀ hs e₀ deposit χ sign)
    (held:WilsonFundedWindowCompany.PhysicalInputs R.kit) (heat:Poetry R.family.path.levels)
    (mark:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (checkoutPrice:Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay)
    (cov:Mallow.RG12.Earned (WilsonCoherentMayerCovarianceCalendar.decal G) R.kit.shape R.alloy.delay)
    (v:ℕ→Gear G→ℝ) (rows:FundedMarkedCoverRows.prices v R.kit)
    (paths:FundedOriginalVacuumPaths.prices R.kit) (d e K load:ℕ) {δ η:ℝ} (dp:0<δ) (fp:0<η):
    let V:=R.family.path.levels
    let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
    let u:=(Bel R.family.book).project 4 v₀
    let labels r:=Fin.cons (α:=fun _:Fin 2=>R.family.label 4) (deposit r (stepField R.family))
      (fun _=>deposit r (freeInput F J Z₀ 4 r u))
    ∃A:ℕ→ℕ,Tendsto A atTop atTop ∧ ∀(q:ℕ) (ε:ℝ),0<ε → ∃credit:Credit,∀ᶠr in trail,
      ∃i,L.level r=i+1 ∧ ∃σ>0,σ⁻¹≤zz V (i+1) ∧ ∀N (live:i+1<N),∃Z:SeriesA G,
        WilsonMatrixTicketLanesVacuumCourse.Filed R d e K load δ η credit i N live σ Z ∧
        (N ≤ i+1+A (i+1) → ∀hr:0<r,Billed R (i+1) N live.le Z σ
          (credit.buy (zz V (i+1))+zz V (i+1)*V.clock.loopCap (i+1)) (2+e)
          (fun p k=>atRef L 4 r (N,p) (labels r k)) (dilate hr φ) (ε*(g r)^q)):=by
  intro V φ u labels
  obtain ⟨_,_,_,_,_,_,_,market,_⟩:=row
  have wb:0<B:=by omega
  have covered:=at_inputs F J Z₀ L lead obey simple wb level e₀ deposit u market
  obtain ⟨A,grows,price⟩:=WilsonMatrixOriginalGermSlabBudget.currency R F L simple slow wb coupling
    (e₀+1) (fun _=>1) (fun _=>by norm_num) φ
  refine ⟨A,grows,?_⟩
  intro q ε ep
  obtain ⟨ξ,positive,invoices⟩:=price q ε ep
  have full:=WilsonMatrixOriginalGermSelectedSpring.purchased R simple slow held heat mark checkoutPrice cov
    v rows paths wide coupling d e K load (q+2*(2*WilsonMatrixOriginalGermNearFields.exponent R (e₀+1)))
    dp fp positive
  obtain ⟨credit,panel⟩:=full
  refine ⟨credit,?_⟩
  filter_upwards [panel,covered,invoices] with r bought inputs settle
  obtain ⟨i,clock,σ,sp,wideσ,all⟩:=bought
  have hj:L.level r=i+1:=(congrFun level r).trans clock
  refine ⟨i,hj,σ,sp,wideσ,?_⟩
  intro N live
  obtain ⟨Z,file,read⟩:=all N live
  refine ⟨Z,file,?_⟩
  intro near hr
  apply spend live.le read
  intro p
  have room:L.level r≤N:=by rw [hj];exact live.le
  have span:N≤L.level r+A (L.level r):=by simpa only [hj] using near
  have cash:=settle hr (congrFun level r) N p (labels r) room span
    (fun k=>by simpa only [mul_one] using inputs k N p room)
  simpa only [hj] using cash

end YM.Integration.WilsonMatrixOriginalGermSlabHearing
