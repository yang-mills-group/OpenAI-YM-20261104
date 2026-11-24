import YM.Integration.WilsonPositionSeparatedProfileLocalFitted

/-! Joint measurability in the genuine held gauge and the sampled compact
forest, including both original frozen-exterior partition functions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileLocalRegular
open Function Filter Set Finset MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots WilsonCoherentForestMeasure WilsonCoherentForestReadout
open WilsonIncidentRegisteredMass WilsonCoherentMeasuredChart WilsonLocalReportingChartFunctions
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {m N per:ℕ}
local notation "coarse" => Config G (R.family.side m per)
local notation "fine" => Config G (R.family.side (m+1) per)
local notation "op" => R.family.path.levels.clock.op m per
local notation "up" => R.family.path.rep N per (m+1)
local notation "down" => R.family.path.rep N per m

private theorem finite_sfinite {α:Type} [MeasurableSpace α] (μ:Measure α) [IsFiniteMeasure μ] : SFinite μ := inferInstance

private theorem weighted (live:m+1≤N) (P:Rep G (R.family.side (m+1) per)) (ep:Measurable P.eval)
    {Ω:Type} [MeasurableSpace Ω] {V:Ω→coarse} {U:Ω→fine} (hv:Measurable V) (hu:Measurable U) :
    Measurable (fun z=>WilsonHeldExteriorLaw.weight R N per m (V z) P (U z)) :=
  (((op).density_meas (R.family.path.levels.blocks m per).branches _).comp (hu.prodMk hv)|>.mul (ep.comp hu)).div
    (((down).envelope (R.makes.wilson.represents N per m ((Nat.le_succ m).trans live)).good).meas.comp hv)

private theorem partition (live:m+1≤N) (P:Rep G (R.family.side (m+1) per)) (ep:Measurable P.eval)
    (T:Forest (op).ratio) (E:Finset T.Free) {Ω:Type} [MeasurableSpace Ω] {V:Ω→coarse}
    {v:Ω→({i:T.Free|i∉E}:Set T.Free)→G.El} (hv:Measurable V) (he:Measurable v) :
    Measurable (fun z=>WilsonForestRetainedFibre.mass R (N:=N) T E (V z) P (v z)) := by
  let μ:=Chart.physical G (↥E)
  have joint : Measurable (fun z : Ω × (↥E→G.El) =>WilsonHeldExteriorLaw.weight R N per m (V z.1) P (filled T E (v z.1) z.2)) :=
    weighted R live P ep (hv.comp measurable_fst) (filled_m T E (he.comp measurable_fst) measurable_snd)
  exact joint.stronglyMeasurable.integral_prod_right' (ν:=μ) |>.measurable

variable {I:Type} [Fintype I]

private theorem corrected (live:m+1<N) (grade:ℕ)
    (fund:Measurable (OriginalMarkedRunAction.approximation R (p:=per) live grade).eval)
    (T:Forest (op).ratio) (B:Finset T.Free) :
    Measurable (fun z:coarse×Sample T B G=>WilsonCoherentRetainedDriver.value R live grade T B z.1 z.2) := by
  let P:=OriginalMarkedRunAction.approximation R (p:=per) live grade
  let E:=moving T B
  have upm:=((up).envelope (R.makes.wilson.represents N per (m+1) live.le).good).meas
  have field:=weighted R live.le P fund (Ω:=coarse×Sample T B G) measurable_fst ((measurable_state T B).comp measurable_snd)
  have trueM:=partition R live.le (up) upm T E (Ω:=coarse×Sample T B G) measurable_fst (measurable_fst.comp measurable_snd)
  have keptM:=partition R live.le P fund T E (Ω:=coarse×Sample T B G) measurable_fst (measurable_fst.comp measurable_snd)
  exact (field.mul trueM).div keptM

theorem original (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (P:ChartRatio G) (hp:LocalRatio P) {ρ:ℝ} (pr:0<ρ) (sr:ρ<Chart.small G P) (q grade:ℕ) :
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (d:I→ℕ) (y:∀i,R.family.label (d i))
      (o:I→Site (R.family.side (m+1) per)) (T:Forest (R.family.path.levels.clock.op m per).ratio)
      (c:ℂ) (χ:ℂ→L[ℝ]ℝ) (H:Config G (R.family.side (m+1) per)→ℝ),Measurable H →
      Measurable (WilsonPositionSeparatedProfileLocalWave.retained R live P q grade ρ d y o T c χ H) := by
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (OriginalMarkedRunAction.calendar R simple marks fees grade)]
    with m offer N live per d y o T c χ H hm
  let B:=incident R T d o
  let A:=R.family.path.levels.clock.op m per
  let Ω:=Config G (R.family.side m per)×Sample T B G
  let θ:=(R.family.path.rep N per (m+1)).p.threshold
  let g:=regulatorRun R.family N per (m+1)
  let β:=R.family.path.β N per (m+1)
  let μ:=law P ρ T B
  letI:IsFiniteMeasure μ:=WilsonCoherentForestMeasure.funded P ρ T B hp pr sr
  let D:=(μ.restrict (panel R m per d o T ρ))
  let dFinite:IsFiniteMeasure D:=by dsimp only [D]; infer_instance
  letI:SFinite D:=@finite_sfinite _ _ D dFinite
  have present:=corrected R live grade (OriginalMarkedRunCovariance.keep_envelope R live (offer N per live)).meas T B
  have driver:Measurable (fun z:Ω=>WilsonLocalRetainedReportingWeight.adjusted P q R live grade T B z.1 z.2) :=
    present.mul (((WilsonLocalConditionalWilsonFactor.regular P q β g T B).comp measurable_snd).div
      ((Chart.Ratio.jacobian_meas hp).comp (measurable_snd.comp measurable_snd)))
  have sample:Measurable (fun z:Ω=>H (state T B z.2)):=hm.comp ((measurable_state T B).comp measurable_snd)
  have model:=measurable_polynomial T B R d θ y o (q+2*reserve R d)
  have test:Measurable (fun z:Ω=>χ (c*polynomial T B R d θ y o (q+2*reserve R d) z.2)):=
    χ.continuous.measurable.comp (measurable_const.mul (model.comp measurable_snd))
  exact ((driver.mul sample).mul test).stronglyMeasurable.integral_prod_right' (ν:=D) |>.measurable

end YM.Integration.WilsonPositionSeparatedProfileLocalRegular
