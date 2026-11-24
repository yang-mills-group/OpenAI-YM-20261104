import YM.Integration.WilsonReportingPrescribedOldRawForecast
import YM.Integration.WilsonReportingPrescribedOldDesign

/-! The forecast relative to the actual original source at its own recorded
birth on the genuine logarithmic upper interval, with all original counterterm costs restored before both regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldUpperForecast
open Filter Lattice Wilson RG Source Marker Precision MergeProof.Accent
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 QLocalVacuumOrderRestriction AnalyticBridge.VerifiedReset.Averaging
open WilsonLimitConstruction Pert.Asymptotics ActualRunInterpolatedPackets QLocalMarkedCouplingDifference
open FullQLocal.PreRun.SuccessiveRequests
open scoped Topology Classical
open WilsonReportingPrescribedOldRawForecast

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] {B : MS.Local.Physical.Deck G}
  (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B)

theorem original (Q : MS.Land.Prescription B) (μ : ℝ) (K₀ : ℕ) :
    ∃ extra : ℕ, ∀ (J₀ : Request V) (A₀ : NumericSchedule R.family J₀),
    ActualRunNativeComponentRecipe.Attached R → RG05Preconstruction.ReadoutPurchase R.b →
    ∀ (caps : Handoff.OutputCapacities) (J : Request V) (A : NumericSchedule R.family J) (K : NumericPrices A) (p r : ℕ), 2 ≤ p+extra → p+extra ≤ J.order → ∀ {ε : ℝ}, 0 < ε →
    ∀ᶠ m : ℕ in atTop, ∀ {b hi : ℕ}, m ≤ hi → WilsonReportHarvestUpperRange.eligible R.family.S b m hi → ∀ (d : LocalFormal.Datum R.family (Stock.census V)), d.level = m → d.cutoff = hi+1 →
      ∀ (Y : Bulk.Chain R.family.path) (F : AnalyticInput J A d) (η : ℝ) (I : FullPreparedInputAt F η)
        (M : FundedPhysicalCatalogue.Purchase caps K F),
      FundedCoverKineticMeasurement.Tested R Y F M hG (fun v => (0 : (J.tests v).Mood)) →
      ∀ S : FundedRenderedBank.Chosen K I M.toCatalogue,
      η ≤ (Currency.g R.family d.cutoff d.period (d.level+1))^2 →
      I.carrier.rep.eval = (R.family.path.rep d.cutoff d.period (d.level+1)).eval →
      ∀ (d₀ : LocalFormal.Datum R.family (Stock.census V)), ActualOriginalQLayout.referenceLevel R u ≤ d₀.level+1 →
      ∀ (o : V → Site (R.family.side (d₀.level+1) d₀.period)) (ks : V → ℕ), (∀i, ks i ≤ K₀) →
      ∀ (origin : QLocalOriginalQHistory.Origin R hG u J₀ A₀ d₀ Q o μ ks I) (t : IndependentTests J.tests),
      ∃ t₀ : IndependentTests (ActualOriginalQPointSetup.request R u J₀).tests, HEq (testInclusion J.tests t) (testInclusion _ t₀) ∧
      ∃ live : d.level ≤ d₀.level+1, ∀ U : Config G (R.family.side d.level d.period), ∀ s : (Stock.census V).Mode,
        let h := ActualOriginalQInitialInput.normalizer R hG u J₀ A₀ d₀ Q o μ ks
        let b := VariableScaling.tests (fun _ => (h:ℂ)) (testInclusion J.tests t)
        let O := S.bank.output
        let x := (plan M.plan (p+extra)).predict d.level+delta (S.vacuum.listing.read S.vacuum.source)
        let q := onRun R d.cutoff d.period d.level O.model r
        let ρ := ((R.family.path.rep d.cutoff d.period d.level).eval U)⁻¹
        let measured := gust R.family.path d.cutoff d.period (d₀.level+1)
          (WilsonReportingPrescribedOldHistory.calendar R origin.period (raw R hG u J₀ d₀ Q o μ ks t₀)) d.level live
        Poly.toll (fun i => F.outputRadii i/F.kernelCosts i) s * ‖(ρ •
          (Poly.pass (q.read b (Currency.gain x) U)*(O.residual.leaf b).density U - measured U)).part s‖ ≤
          ε*(regulatorRun R.family d.cutoff d.period (d.level+1))^((p:ℝ)+1-J.eta) := by
  obtain ⟨extra, grants⟩ := WilsonReportingPrescribedOldDesign.original R hG u Q μ K₀
  refine ⟨extra,?_⟩
  intro J₀ A₀ hT readout caps J A K p r hp hq ε ep
  obtain ⟨δ,dp, cash⟩ := grants J₀ A₀ ep
  filter_upwards [cash, WilsonReportingPrescribedOldRawForecast.original R hG u J₀ A₀ hT readout caps J A K hp hq r dp]
    with m income plan
  intro b hi upper window d date cutoff Y F η I M tested S paid same d₀ ref o ks allowed origin t
  obtain ⟨t₀,test,live,physical⟩ := plan d date Y F η I M tested S paid same d₀ ref Q o μ ks origin t
  have sourceDate : d₀.cutoff = hi+1 := origin.cutoff.symm.trans cutoff
  refine ⟨t₀,test,live,?_⟩
  intro U s
  have charged := income upper window d₀ sourceDate o ks allowed s ((p:ℝ)+1-J.eta)
  have exponents : (((p+extra:ℕ):ℝ)+1-J.eta) = ((p:ℝ)+1-J.eta)+(extra:ℝ) := by push_cast;ring
  rw [←date, ←origin.period, ←origin.cutoff, ←exponents] at charged
  exact (physical U s).trans charged

end YM.Integration.WilsonReportingPrescribedOldUpperForecast
