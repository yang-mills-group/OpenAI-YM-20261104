import YM.Integration.WilsonInvariantActionTransportedOld
import YM.Integration.ManuscriptQLocalPrescribedRawMoment

/-! The high coupling grades of the independent planted Q source against
the complete centered previous regular mark on the true lower Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionPreviousQMoment
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Shoot Marker OPE.Therm Comparison.RG02
open Comparison.Density.RenderM Comparison.Density.RenderM.Token ActualRunPacketRetuning
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Pert.Asymptotics
open ManuscriptQLocalOriginalConditionalTail ManuscriptQLocalRegularConditional ManuscriptQLocalSourceFourier
open RG.Supply Next.Rank Push.GridApprox WardBin.Wheels
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Scheduling Next.Scheduling.Clock
open Push.PriceCompiler Next.Foundations Source RG3.Script.Picnic PhysicalNext.ThroughLaunch WilsonLimitConstruction
open Actual Order IterationFour IterationFour.Vacuum
open WilsonInvariantActionTransportedOld WilsonInvariantActionMixedMaterial
open scoped Classical BigOperators Topology
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {B:MS.Local.Physical.Deck G}
  (R:Run G) (simple:G.Simple) (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
local notation "JB" => ActualOriginalQPointSetup.request R u J
local notation "AB" => ActualOriginalQInitialInput.schedule R simple u J A
local notation "census₀" => Stock.census V

set_option backward.isDefEq.respectTransparency false in
theorem purchased (warm:Poetry R.family.path.levels) (k:ℕ) {δ:ℝ} (hδ:0<δ):
    ∀ᶠ m:ℕ in atTop,∀(d:LocalFormal.Datum R.family census₀),d.level=m→
    ∀(Q:MS.Land.Prescription B) (o:V→Site (R.family.side (d.level+1) d.period)) (strength:ℝ) (orders:V→ℕ)
      (stages:WithStage R.metals.p OriginalRunConstruction.originalOrders)
      (beginning:ActualOriginalQInitialPreparation.start R simple u J A stages ≤ d.level)
      (period:(JB).physicalPeriodLower ≤ (R.family.S.period d.period).val)
      (x:IndependentTests (JB).tests) (s:(census₀).Mode),
    let F:=ActualOriginalQInitialPreparation.analyticInput R simple u J A d Q o strength orders stages beginning period
    let g:=regulatorRun R.family d.cutoff d.period (d.level+1)
    let B₀:=(R.family.path.rep d.cutoff d.period (d.level+1)).p
    let w:=fun v=>F.inputRadii v/F.kernelCosts v
    let D:=ManuscriptQLocalShiftLedger.weight (fun _:V=>F.packets.powerCap+F.packets.rankCap) s
    let phase z U:=Extra.Trajectories.connected (moment R.family (N:=d.cutoff) U (source F.packets B₀ g x) z)
    let raw:=ManuscriptQLocalMeasuredMarkTransport.logarithm R.family (N:=d.cutoff)
      (F.packets.read (testInclusion (JB).tests x) g)
    let μ:=scene R.family.path d.cutoff d.period d.level
    let C:=ManuscriptQLocalRegularCalendar.constant (J:=JB) (census₀)
    ∃q:Config G (R.family.side d.level d.period)→Polynomial ℂ,
      (∀U,(q U).natDegree≤D) ∧ (∀U z,(q U).eval z=(phase z U).part s) ∧
      Measurable (fun U=>ManuscriptQLocalConditionalGradeTail.low (q U) D k) ∧
      ∀ l (earlier:d.level ≤ l) (live:l≤d.cutoff) (_birth:R.family.ref 4 ≤ l)
        (v:R.family.label 4) (y:Site (R.family.side l d.period)) (I:Set ℕ),
        ‖∫U,((Poly.toll w s:ℂ)*((raw U).part s-ManuscriptQLocalConditionalGradeTail.low (q U) D k))*
             centered R earlier live v y I U ∂μ‖ ≤
          (2*budget v l d.cutoff d.period)*(2*(1+C)*g^((k+1:ℕ)-δ:ℝ)):=by
  filter_upwards [ManuscriptQLocalPrescribedRawMoment.measured (Γ:=census₀) R (AB) simple warm k 0 hδ] with m paid
  intro d same Q o strength orders stages beginning period x s F g B₀ w D phase raw μ C
  have bare:ManuscriptQLocalOriginalSourceGrade.Bare F:=by
    apply ManuscriptQLocalOriginalSourceGrade.zero_power
    intro i
    rfl
  obtain ⟨q,hd,hp,meas,int,charge⟩:=paid d same F bare x s
  refine ⟨q,hd,hp,meas,?_⟩
  intro l earlier live birth v y I
  let remainder U:ℂ:=(Poly.toll w s:ℂ)*((raw U).part s-ManuscriptQLocalConditionalGradeTail.low (q U) D k)
  have positive:0≤Poly.toll w s:=(Poly.worth F.input_paid.positive s).le
  have normal(U):‖remainder U‖=Poly.toll w s*‖(raw U).part s-ManuscriptQLocalConditionalGradeTail.low (q U) D k‖:=by
    simp only [remainder,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg positive]
  have integrable:Integrable (fun U=>‖remainder U‖) μ:=by
    simpa only [normal,Nat.zero_add,pow_one] using int
  have total:(∫U,‖remainder U‖ ∂μ)≤2*(1+C)*g^((k+1:ℕ)-δ:ℝ):=by
    simpa only [normal,Nat.zero_add,pow_one] using charge
  have c0:0≤budget v l d.cutoff d.period:=(norm_nonneg _).trans
    ((WilsonInvariantActionMixedMaterial.filed R.makes live birth v y I).2.2.2 1)
  exact (billed R earlier live birth v y I remainder integrable).trans
    (mul_le_mul_of_nonneg_left total (mul_nonneg (by norm_num) c0))

end YM.Integration.WilsonInvariantActionPreviousQMoment
