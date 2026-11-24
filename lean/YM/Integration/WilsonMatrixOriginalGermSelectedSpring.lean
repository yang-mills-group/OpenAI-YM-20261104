import YM.Integration.WilsonMatrixOriginalGermConditionalMask
import YM.Integration.WilsonMatrixTicketLanesVacuumCourse

/-! One original spring credit and one series for every upper cutoff are
filed before the period. The complete physical two-mark hearing on this
same series spends the measured running coupling at the prescribed date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermSelectedSpring
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
variable {G:Gauge} (R:Run G)

def Signed (j N:ℕ) (live:j≤N) (Z:SeriesA G) (σ C:ℝ) (load:ℕ) (income:ℝ):Prop:=
  ∀p (x:Site (R.family.side j p)) m (lower:m≤j) (v:Fin 2→R.family.label 4) (φ:Test 2),
    let t:=regulatorRun R.family N p j
    let S:=fun U=>springAt R N p j load Z t x U
    let M:=fun U=>maskedSpringAt R N p j load Z σ C t x U
    let W:=fun U=>((M U-S U:ℝ):ℂ)
    let amount:=bill R lower live W v φ
    HasDerivAt (fun s=>hearing R lower live (fun U=>((-S U:ℝ):ℂ)) v φ s-
      hearing R lower live (fun U=>((-M U:ℝ):ℂ)) v φ s) amount 0 ∧
      amount=(∫U,response R lower live v φ U*W U ∂scene R.family.path N p j) ∧
      ‖amount‖≤cost R (p:=p) lower live v φ*income

theorem spend {j N:ℕ} (live:j≤N) {Z:SeriesA G} {σ C:ℝ} {r q:ℕ} {ε η:ℝ}
    (sold:Sale R j N live Z σ C r q ε) (cap:∀p,ε*(regulatorRun R.family N p j)^q≤η):
    Signed R j N live Z σ C r η:=by
  intro p x m lower v φ t S M W amount
  have h:=sold.2 p x m lower v φ
  exact ⟨(sold.1 p x m lower v φ).1,h.1,h.2.trans (mul_le_mul_of_nonneg_left (cap p) (Real.sqrt_nonneg _))⟩

theorem purchased (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
    (held:WilsonFundedWindowCompany.PhysicalInputs R.kit) (heat:Poetry R.family.path.levels)
    (mark:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (checkoutPrice:Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay)
    (cov:Mallow.RG12.Earned (WilsonCoherentMayerCovarianceCalendar.decal G) R.kit.shape R.alloy.delay)
    (v:ℕ→Gear G→ℝ) (rows:FundedMarkedCoverRows.prices v R.kit)
    (paths:FundedOriginalVacuumPaths.prices R.kit) {B:ℕ} (wide:17≤B)
    {g:ℝ→ℝ} (coupling:Coupling G g) (d e K load q:ℕ) {δ η ε:ℝ} (dp:0<δ) (fp:0<η) (ep:0<ε):
    let V:=R.family.path.levels
    let stop:=WilsonMeasuredWindow.stop V simple B
    ∃credit:Credit,∀ᶠr in trail,∃i,stop r=i+1 ∧ ∃σ>0,σ⁻¹≤zz V (i+1) ∧
      ∀N (live:i+1<N),∃Z:SeriesA G,WilsonMatrixTicketLanesVacuumCourse.Filed R d e K load δ η credit i N live σ Z ∧
        Signed R (i+1) N live.le Z σ (credit.buy (zz V (i+1))+zz V (i+1)*V.clock.loopCap (i+1)) (2+e) (ε*(g r)^q):=by
  intro V stop
  obtain ⟨credit,course⟩:=WilsonRegisteredSpringPriorCourse.original R simple slow held mark checkoutPrice cov d v rows paths e K load dp fp
  have positive:0<(2:ℝ)^q:=by positivity
  have mask:=WilsonMatrixOriginalGermConditionalMask.purchased R simple slow heat v rows credit (3+e) (meterPre (3+e)) (2+e) q (div_pos ep positive)
  obtain ⟨after,ready⟩:=eventually_atTop.mp (course.and mask)
  have grows:Tendsto stop trail atTop:=WilsonMeasuredWindow.stop_tendsto _ simple B (by omega)
  have hB:0<B:=by omega
  have hot:=(WilsonPhysicalCutoffCurrency.temperature R simple slow hB g coupling).eventually
    (lt_mem_nhds (show (1/2:ℝ)<1 by norm_num))
  refine ⟨credit,?_⟩
  filter_upwards [grows.eventually_ge_atTop (after+1),hot,coupling.positive] with r late temp gp
  let i:=stop r-1
  have eq:stop r=i+1:=by dsimp [i];omega
  have hi:after ≤ i:=by omega
  obtain ⟨issued,available⟩:=ready i hi
  obtain ⟨σ,sp,wide,full⟩:=issued
  refine ⟨i,eq,σ,sp,wide,?_⟩
  intro N live
  obtain ⟨Z,grades,pre,len,draw,period,match_,root,invoice,guides⟩:=full N live
  refine ⟨Z,⟨grades,pre,len,draw,period,match_,root,invoice,guides⟩,?_⟩
  have low (a)(ha:a∈Z):0<a.grade:=by have:=grades a ha;omega
  apply spend R live.le (available N live σ sp wide Z draw len low (fun a ha=>(pre a ha).le))
  intro p
  have warm:1/2<V.clock.hatBeta (i+1)*(g r)^2:=by simpa only [←eq] using temp
  have used:=coupling_bound R simple (p:=p) le_rfl live.le gp warm
  have nz:0≤regulatorRun R.family N p (i+1):=(IterationFour.Currency.g_pos R.makes N p (i+1) live.le).le
  calc
    (ε/2^q)*(regulatorRun R.family N p (i+1))^q≤(ε/2^q)*(2*g r)^q:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ nz used _) (div_nonneg ep.le positive.le)
    _=ε*(g r)^q:=by rw [mul_pow,←mul_assoc,div_mul_cancel₀ _ positive.ne']

end YM.Integration.WilsonMatrixOriginalGermSelectedSpring
