import YM.Integration.QLocalOriginalQHistory

/-! Pointwise measured higher-order readout on each actual Q history.
The original test in every slot is arbitrary. Its own envelope is selected
before the field and all mode coefficients are restored. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalOriginalQReadout

open Filter Lattice Wilson RG Marker Precision LocalComparison LocalComparison.Global
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 QLocalVacuumOrderRestriction QLocalReceivedWilsonState QLocalOriginalQHistory
open AnalyticBridge.VerifiedReset.Averaging WilsonLimitConstruction Pert.Asymptotics
open ActualRunInterpolatedPackets QLocalMarkedCouplingDifference
open scoped Topology Classical

variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V] {B:MS.Local.Physical.Deck G}

theorem born (R:Run G) (hG:G.Simple) (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
    (ord:∀ k,k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power)
    {m:ℕ} (H:QLocalOriginalQState.Original R hG u J A ord m)
    (d:LocalFormal.Datum R.family (Stock.census V)) (hm:d.level=m)
    (Q:MS.Land.Prescription B) (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (ks:V→ℕ)
    (hp:(ActualOriginalQPointSetup.request R u J).physicalPeriodLower≤(R.family.S.period d.period).val)
    (top:d.cutoff=d.level+1) :
    ∃ first:ActualOriginalQInitialInput.start R hG u J A ord≤d.level,
    ∃ I:FullPreparedInputAt (ActualOriginalQInitialInput.input R hG u J A d Q o μ ks ord first hp) 0,
      Retained.NativeIntake I ∧ I.carrier.rep=R.family.path.rep d.cutoff d.period (d.level+1) ∧
      I.regularPrice=0 ∧ I.forcedPrice=0 ∧ Origin R hG u J A d Q o μ ks I := by
  obtain ⟨first,I,intake,rep,reg,force,state⟩:=H d hm Q o μ ks hp top
  exact ⟨first,I,intake,rep,reg,force,QLocalOriginalQHistory.start R hG u J A d Q o μ ks state⟩

variable {J:Request V} (R:Run G) (hG:G.Simple) (u:V→MS.Rake.Label B)
    (J₀:Request V) (A₀:NumericSchedule R.family J₀) (hT:ActualRunNativeComponentRecipe.Attached R)
    (readout:RG05Preconstruction.ReadoutPurchase R.b) (caps:Handoff.OutputCapacities)
    (A:NumericSchedule R.family J) (K:NumericPrices A)

include hT readout

theorem selected {p:ℕ} (hp:2≤p) (hq:p≤J.order) (r:ℕ) {ε:ℝ} (hε:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀ (d:LocalFormal.Datum R.family (Stock.census V)),d.level=m →
      ∀ (Y:Bulk.Chain R.family.path) (F:AnalyticInput J A d) (η:ℝ) (I:FullPreparedInputAt F η)
        (M:FundedPhysicalCatalogue.Purchase caps K F),
      FundedCoverKineticMeasurement.Tested R Y F M hG (fun v=>(0:(J.tests v).Mood)) →
      ∀ S:FundedRenderedBank.Chosen K I M.toCatalogue,
      η≤(Currency.g R.family d.cutoff d.period (d.level+1))^2 →
      I.carrier.rep.eval=(R.family.path.rep d.cutoff d.period (d.level+1)).eval →
      let O:=S.bank.output
      let Q:=onRun R d.cutoff d.period d.level O.model r
      let x:=(plan M.plan p).predict d.level+delta (S.vacuum.listing.read S.vacuum.source)
      let w:=fun v=>F.outputRadii v/F.kernelCosts v
      let f:=regulatorRun R.family d.cutoff d.period (d.level+1)
      ∀ d₀:LocalFormal.Datum R.family (Stock.census V),ActualOriginalQLayout.referenceLevel R u≤d₀.level+1 →
      ∀ (P:MS.Land.Prescription B) (o:V→Site (R.family.side (d₀.level+1) d₀.period))
        (μ:ℝ) (orders:V→ℕ), Origin R hG u J₀ A₀ d₀ P o μ orders I →
      ∀ t:TestSpace J.tests,∃ h:V→ℝ, (∀v,0<h v) ∧ ∀ U s,
      let ρ:=((R.family.path.rep d.cutoff d.period d.level).eval U)⁻¹
      Poly.toll w s*‖(ρ • (Poly.pass (Q.read t (Currency.gain x) U)*(O.residual.leaf t).density U-
        (O.output.leaf t).density U)).part s‖≤envelopeProduct h s*(ε*f^((p:ℝ)+1-J.eta)) := by
  filter_upwards [QLocalOriginalQEnvelope.selected R hG u J₀ A₀ hT readout caps A K hp hq r hε]
    with m issue d hm Y F η I M contact S hη fine
  dsimp only
  intro d₀ ref P o μ orders origin t
  obtain ⟨source,st,aligned⟩:=origin.replay
  obtain ⟨h,hh,x,hx⟩:=FundedIndependentTestScaling.represent t
  obtain ⟨x₀,same⟩:=QLocalOriginalQHistory.unit origin.tests x
  have grow:VariableScaling.tests (fun v=>(h v:ℂ)) (testInclusion J.tests x)=t:=by
    rw [hx]
    simpa only [FundedIndependentTestScaling.shrink,inv_inv] using VariableScaling.tests_inverse
      (fun v=>(h v:ℂ)⁻¹) (fun v=>inv_ne_zero (Complex.ofReal_ne_zero.mpr (hh v).ne')) t
  refine ⟨h,hh,?_⟩
  simpa only [grow] using issue d hm Y F η I M contact S hη fine d₀ origin.cutoff origin.period ref
    P o μ orders source st x x₀ (aligned _ _ same) h hh

end YM.Integration.QLocalOriginalQReadout
