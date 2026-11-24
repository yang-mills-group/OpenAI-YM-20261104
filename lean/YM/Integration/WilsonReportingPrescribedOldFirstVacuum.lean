import YM.Integration.QLocalOriginalQReadout
import YM.Integration.WilsonReportingPrescribedOldFirstReceipt

/-! The receiving physical vacuum and its bought calibration on the actual
first successor of the prescribed marked source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldFirstVacuum
open Filter Lattice Wilson RG Source Marker Precision MergeProof.Accent
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 WilsonLimitConstruction FullQLocal.PreRun.SuccessiveRequests
open scoped Topology Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} (R : Run G)
  {J : Request V} {A : NumericSchedule R.family J} {K : NumericPrices A}
  {d : LocalFormal.Datum R.family Γ} {F : AnalyticInput J A d} {η : ℝ} {I : FullPreparedInputAt F η}
  {caps : Handoff.OutputCapacities} {M : FundedPhysicalCatalogue.Purchase caps K F}
  {S : FundedRenderedBank.Chosen K I M.toCatalogue} {bank : FundedRenderedBank.Canonical S}
  {r m q : ℕ} {dm : d.level=m+1} {A' : NumericSchedule R.family (nextRequest J caps r)}
  {W : Bulk.Colors Γ G (R.family.side (m+1) d.period)} {x : Exterior.fieldDir G (R.family.side m d.period) 1}
  {next : FundedCoverStepPrice.Receipt R M S bank r dm A' W x q}

/-- The equality uses the genuine preceding bank's vacuum output at the same
period and cutoff. -/
theorem earlier (received : FundedCoverFlatStep.Accepted R next)
    (physical : I.carrier.rep.eval=(R.family.path.rep d.cutoff d.period (d.level+1)).eval) :
    received.input.carrier.rep.eval=(R.family.path.rep d.cutoff d.period (m+1)).eval := by
  rcases d with ⟨N,per,level,below,forest,tag,colors,held⟩
  dsimp only at dm
  subst level
  have carried := eq_of_heq received.carrier
  rw [carried]
  exact bank.bank.output.output_vacuum R.makes below physical

/-- One date before every true sampled origin pays the quadratic inlet demanded
by the native higher-order independent comparison. -/
theorem calibrated (hG : G.Simple) (attached : ActualRunNativeComponentRecipe.Attached R)
    (readout : RG05Preconstruction.ReadoutPurchase R.b) (caps : Handoff.OutputCapacities)
    (J : Request V) (A : NumericSchedule R.family J) (K : NumericPrices A) (r : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ N per, m<N → J.physicalPeriodLower ≤ (R.family.S.period per).val →
      FundedCoverKineticWindow.next R caps A K (Γ:=Γ) N per m ≤ (Currency.g R.family N per (m+1))^2 := by
  obtain ⟨first,bought⟩ := (FundedCoverKineticWindow.uniformly_flat R caps A K (Γ:=Γ) hG attached readout
    (nextRequest J caps r)).2 2
  filter_upwards [eventually_ge_atTop first] with m reached N per live period
  exact bought N per m reached live period

end YM.Integration.WilsonReportingPrescribedOldFirstVacuum
