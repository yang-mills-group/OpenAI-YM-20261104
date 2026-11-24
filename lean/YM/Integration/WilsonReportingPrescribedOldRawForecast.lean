import YM.Integration.WilsonReportingPrescribedOldHistory
import YM.Integration.QLocalOriginalQEnvelope

/-! The forecast relative to the actual original source at its own recorded
birth, with the full unscaled original fee in every licensed face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldRawForecast
open Filter Lattice Wilson RG Source Marker Precision MergeProof.Accent
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 QLocalVacuumOrderRestriction AnalyticBridge.VerifiedReset.Averaging
open WilsonLimitConstruction Pert.Asymptotics ActualRunInterpolatedPackets QLocalMarkedCouplingDifference
open FullQLocal.PreRun.SuccessiveRequests
open scoped Topology Classical
open private calendar_eq from YM.Integration.WilsonReportingPrescribedOldHistory
open private scaled from YM.Integration.QLocalOriginalQHistory

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] {B : MS.Local.Physical.Deck G}
  (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B) (J₀ : Request V) (A₀ : NumericSchedule R.family J₀)
  (hT : ActualRunNativeComponentRecipe.Attached R) (readout : RG05Preconstruction.ReadoutPurchase R.b)
  (caps : Handoff.OutputCapacities) (J : Request V) (A : NumericSchedule R.family J) (K : NumericPrices A)

def raw (d₀ : LocalFormal.Datum R.family (Stock.census V)) (Q : MS.Land.Prescription B)
    (o : V → Site (R.family.side (d₀.level+1) d₀.period)) (μ : ℝ) (ks : V → ℕ)
    (t₀ : IndependentTests (ActualOriginalQPointSetup.request R u J₀).tests) :=
  let D := ActualOriginalQPointSetup.pointDatum R J₀ d₀.period (d₀.level+1) o
  ((ActualOriginalQInput.input Q D u (μ-R.family.S.scale d₀.cutoff) ks hG d₀.cutoff d₀.below).leaf
    (testInclusion _ t₀)).density

include hT readout in
/-- The prescribed source at its own birth is the complete physical target at
every earlier state. The normalization cost is explicit on every face. -/
theorem original {p : ℕ} (hp : 2 ≤ p) (hq : p ≤ J.order) (r : ℕ) {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (d : LocalFormal.Datum R.family (Stock.census V)), d.level = m →
      ∀ (Y : Bulk.Chain R.family.path) (F : AnalyticInput J A d) (η : ℝ) (I : FullPreparedInputAt F η)
        (M : FundedPhysicalCatalogue.Purchase caps K F),
      FundedCoverKineticMeasurement.Tested R Y F M hG (fun v => (0 : (J.tests v).Mood)) →
      ∀ S : FundedRenderedBank.Chosen K I M.toCatalogue,
      η ≤ (Currency.g R.family d.cutoff d.period (d.level+1))^2 →
      I.carrier.rep.eval = (R.family.path.rep d.cutoff d.period (d.level+1)).eval →
      ∀ (d₀ : LocalFormal.Datum R.family (Stock.census V)), ActualOriginalQLayout.referenceLevel R u ≤ d₀.level+1 →
      ∀ (Q : MS.Land.Prescription B) (o : V → Site (R.family.side (d₀.level+1) d₀.period)) (μ : ℝ) (ks : V → ℕ)
        (origin : QLocalOriginalQHistory.Origin R hG u J₀ A₀ d₀ Q o μ ks I) (t : IndependentTests J.tests),
      ∃ t₀ : IndependentTests (ActualOriginalQPointSetup.request R u J₀).tests, HEq (testInclusion J.tests t) (testInclusion _ t₀) ∧
      ∃ live : d.level ≤ d₀.level+1, ∀ U : Config G (R.family.side d.level d.period), ∀ s : (Stock.census V).Mode,
        let h := ActualOriginalQInitialInput.normalizer R hG u J₀ A₀ d₀ Q o μ ks
        let b := VariableScaling.tests (fun _ => (h:ℂ)) (testInclusion J.tests t)
        let O := S.bank.output
        let x := (plan M.plan p).predict d.level+delta (S.vacuum.listing.read S.vacuum.source)
        let q := onRun R d.cutoff d.period d.level O.model r
        let ρ := ((R.family.path.rep d.cutoff d.period d.level).eval U)⁻¹
        let measured := gust R.family.path d.cutoff d.period (d₀.level+1)
          (WilsonReportingPrescribedOldHistory.calendar R origin.period (raw R hG u J₀ d₀ Q o μ ks t₀)) d.level live
        Poly.toll (fun i => F.outputRadii i/F.kernelCosts i) s * ‖(ρ •
          (Poly.pass (q.read b (Currency.gain x) U)*(O.residual.leaf b).density U - measured U)).part s‖ ≤
          h^s.val.card*(ε*(regulatorRun R.family d.cutoff d.period (d.level+1))^((p:ℝ)+1-J.eta)) := by
  filter_upwards [QLocalOriginalQEnvelope.selected R hG u J₀ A₀ hT readout caps A K hp hq r ep] with m buy
  intro d level Y F η I M tested S paid same d₀ ref Q o μ ks origin t
  obtain ⟨t₀, unit⟩ := QLocalOriginalQHistory.unit origin.tests t
  obtain ⟨v, state, history⟩ := origin.replay
  let h := ActualOriginalQInitialInput.normalizer R hG u J₀ A₀ d₀ Q o μ ks
  have hpos : 0<h := zero_lt_one.trans_le (le_max_left _ _)
  let b := VariableScaling.tests (fun _ => (h:ℂ)) (testInclusion J.tests t)
  let b₀ := VariableScaling.tests (fun _ => (h:ℂ)) (testInclusion _ t₀)
  have purchase := buy d level Y F η I M tested S paid same d₀ origin.cutoff origin.period ref Q o μ ks
    v state t t₀ (history _ _ unit) (fun _ => h) (fun _ => hpos)
  let live : d.level ≤ d₀.level+1 := (Nat.le_succ _).trans state.before
  have issued := QLocalReceivedWilsonState.output state M.toCatalogue S.bank b
  have actual : v b = WilsonReportingPrescribedOldHistory.calendar R origin.period (raw R hG u J₀ d₀ Q o μ ks t₀) := by
    have filed := history b b₀ (scaled origin.tests (fun _ => (h:ℂ)) unit)
    have unscaled : ((ActualOriginalQInitialPreparation.input R hG u J₀ A₀ d₀ Q o μ ks).leaf b₀).density =
        raw R hG u J₀ d₀ Q o μ ks t₀ :=
      funext (QLocalOriginalQEnvelope.original R hG u J₀ A₀ d₀ Q o μ ks (testInclusion _ t₀))
    exact eq_of_heq ((filed.trans (heq_of_eq unscaled)).trans (calendar_eq R origin.period _))
  refine ⟨t₀,unit,live,?_⟩
  intro U s
  have visited : (S.bank.output.output.leaf (VariableScaling.tests (fun _ => (h:ℂ)) (testInclusion J.tests t))).density U =
      gust R.family.path d.cutoff d.period (d₀.level+1)
        (WilsonReportingPrescribedOldHistory.calendar R origin.period (raw R hG u J₀ d₀ Q o μ ks t₀)) d.level live U := by
    change (S.bank.output.output.leaf b).density U = _
    rw [issued,actual]
  simpa only [visited, envelopeProduct, Finset.prod_const] using purchase U s

end YM.Integration.WilsonReportingPrescribedOldRawForecast
