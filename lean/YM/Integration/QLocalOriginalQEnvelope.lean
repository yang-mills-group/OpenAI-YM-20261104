import YM.Integration.QLocalOriginalQForecast
import YM.Integration.QLocalRestoredMarkedBill

/-! The original Wilson source after independent input-envelope restoration,
including every compulsory coefficient in each marked output mode. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalOriginalQEnvelope
open YM.Integration.QLocalOriginalQForecast

open Filter Lattice Wilson RG Marker Precision LocalComparison LocalComparison.Global
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 QLocalVacuumOrderRestriction MergeProof.Accent QLocalReceivedWilsonState
open AnalyticBridge.VerifiedReset.Averaging WilsonLimitConstruction Pert.Asymptotics
open ActualRunInterpolatedPackets QLocalMarkedCouplingDifference
open scoped Topology Classical

open FundedIndependentTestScaling

variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V] {B:MS.Local.Physical.Deck G}

theorem original (R:Run G) (hG:G.Simple) (u:V→MS.Rake.Label B) (J:Request V)
    (A:NumericSchedule R.family J) (d:LocalFormal.Datum R.family (Stock.census V)) (P:MS.Land.Prescription B)
    (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (orders:V→ℕ)
    (x:TestSpace (ActualOriginalQPointSetup.request R u J).tests) (U:Config G (R.family.side (d.level+1) d.period)) :
    let H:=ActualOriginalQInitialInput.normalizer R hG u J A d P o μ orders
    ((ActualOriginalQInitialPreparation.input R hG u J A d P o μ orders).leaf
      (VariableScaling.tests (fun _=>(H:ℂ)) x)).density U=
        ((ActualOriginalQInput.input P (ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o)
          u (μ-R.family.S.scale d.cutoff) orders hG d.cutoff d.below).leaf x).density U := by
  let H:=ActualOriginalQInitialInput.normalizer R hG u J A d P o μ orders
  have hp:0<H:=zero_lt_one.trans_le (le_max_left _ _)
  have prepared := ActualOriginalQInitialPreparation.input_density R hG u J A d P o μ orders
    (VariableScaling.tests (fun _ => (H:ℂ)) x) U
  have undo : VariableScaling.tests (ActualOriginalQInitialInput.scales R hG u J A d P o μ orders)
      (VariableScaling.tests (fun _ => (H:ℂ)) x) = x :=
    VariableScaling.tests_inverse (fun _ => (H:ℂ))
      (fun _ => Complex.ofReal_ne_zero.mpr hp.ne') x
  let raw := ActualOriginalQInput.input P
    (ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o)
    u (μ-R.family.S.scale d.cutoff) orders hG d.cutoff d.below
  exact prepared.trans (congrArg (fun t => (raw.leaf t).density U) undo)

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
      ∀ (d₀:LocalFormal.Datum R.family (Stock.census V)),d.cutoff=d₀.cutoff → d.period=d₀.period →
      ActualOriginalQLayout.referenceLevel R u≤d₀.level+1 →
      ∀ (P:MS.Land.Prescription B) (o:V→Site (R.family.side (d₀.level+1) d₀.period))
        (μ:ℝ) (orders:V→ℕ)
        (source:TestSpace J.tests → Config G (R.family.side (d₀.level+1) d.period)→Poly (Stock.census V)),
      State I (d₀.level+1) source →
      ∀ (t:IndependentTests J.tests)
        (t₀:IndependentTests (ActualOriginalQPointSetup.request R u J₀).tests),
      let v:=testInclusion J.tests t
      let v₀:=testInclusion _ t₀
      HEq (source v) ((ActualOriginalQInitialPreparation.input R hG u J₀ A₀ d₀ P o μ orders).leaf v₀).density →
      ∀ (h:V→ℝ), (∀v,0<h v) → ∀ U s,
      let b:=VariableScaling.tests (fun v=>(h v:ℂ)) v
      let ρ:=((R.family.path.rep d.cutoff d.period d.level).eval U)⁻¹
      Poly.toll w s*‖(ρ • (Poly.pass (Q.read b (Currency.gain x) U)*(O.residual.leaf b).density U-
        (O.output.leaf b).density U)).part s‖≤envelopeProduct h s*(ε*f^((p:ℝ)+1-J.eta)) := by
  obtain ⟨_,_,_,measure⟩:=QLocalPhysicalRetunedMeasurement.selected (Γ:=Stock.census V) R hG hT readout caps A K hp hq r
  filter_upwards [QLocalOriginalQForecast.selected R hG u J₀ A₀ hT readout caps A K hp hq r hε,measure]
    with m price multi d hm Y F η I M contact S hη fine
  dsimp only
  intro d₀ hn hb ref P o μ orders source L t t₀ chosen h hh U s
  let v:=testInclusion J.tests t
  let b:=VariableScaling.tests (fun i=>(h i:ℂ)) v
  let ρ:=((R.family.path.rep d.cutoff d.period d.level).eval U)⁻¹
  let c:=regulatorRun R.family d.cutoff d.period d.level
  have hc:0<c:=Currency.g_pos R.makes _ _ _ d.below.le
  obtain ⟨paid,fields,_⟩:=multi d hm Y F η I M contact S hη fine
  have unit:=price d hm Y F η I M contact S hη fine d₀ hn hb ref P o μ orders source L t t₀ chosen U
  have narrow:shrink h b=v:=VariableScaling.tests_inverse (fun i=>(h i:ℂ))
    (fun i=>Complex.ofReal_ne_zero.mpr (hh i).ne') v
  have localBill:=QLocalRestoredMarkedBill.component
    (a:=ε*(regulatorRun R.family d.cutoff d.period (d.level+1))^((p:ℝ)+1-J.eta))
    S.bank.output.output S.bank.output_multilinear
    _ paid hc.ne' h hh b U (ρ:ℂ) s
  unfold QLocalRestoredMarkedBill.error at localBill
  rw [narrow,←(fields b U).2,←(fields v U).2] at localBill
  simpa only [Complex.coe_smul] using localBill (by simpa only [Complex.coe_smul] using unit)

end YM.Integration.QLocalOriginalQEnvelope

