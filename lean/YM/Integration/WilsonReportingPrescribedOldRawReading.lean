import YM.Integration.WilsonReportingPrescribedOldRawForecast
import YM.Integration.ActualWilsonAbsoluteTransport

/-! The unscaled registered residual at a genuinely earlier date on the
original Wilson course, with the true lower conditional of a correlated
spectator as its price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldRawReading
open Filter Lattice Wilson RG Source Marker Precision MergeProof.Accent
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 QLocalVacuumOrderRestriction AnalyticBridge.VerifiedReset.Averaging
open WilsonLimitConstruction Pert.Asymptotics ActualRunInterpolatedPackets QLocalMarkedCouplingDifference
open FullQLocal.PreRun.SuccessiveRequests
open scoped Topology Classical
open MeasureTheory MergeProof OPE.Therm

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] {B : MS.Local.Physical.Deck G}
  (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B) (J₀ : Request V) (A₀ : NumericSchedule R.family J₀)
  (caps : Handoff.OutputCapacities) (J : Request V) (A : NumericSchedule R.family J) (K : NumericPrices A)

def difference (d : LocalFormal.Datum R.family (Stock.census V)) (F : AnalyticInput J A d)
    {η : ℝ} (I : FullPreparedInputAt F η) (M : FundedPhysicalCatalogue.Purchase caps K F)
    (S : FundedRenderedBank.Chosen K I M.toCatalogue) (p r : ℕ)
    (d₀ : LocalFormal.Datum R.family (Stock.census V)) (period : d.period = d₀.period)
    (live : d.level ≤ d₀.level+1) (Q : MS.Land.Prescription B)
    (o : V → Site (R.family.side (d₀.level+1) d₀.period)) (μ : ℝ) (ks : V → ℕ)
    (t : IndependentTests J.tests) (t₀ : IndependentTests (ActualOriginalQPointSetup.request R u J₀).tests)
    (U : Config G (R.family.side d.level d.period)) : Poly (Stock.census V) :=
  let h := ActualOriginalQInitialInput.normalizer R hG u J₀ A₀ d₀ Q o μ ks
  let b := VariableScaling.tests (fun _ => (h:ℂ)) (testInclusion J.tests t)
  let O := S.bank.output
  let x := (plan M.plan p).predict d.level+delta (S.vacuum.listing.read S.vacuum.source)
  let q := onRun R d.cutoff d.period d.level O.model r
  ((R.family.path.rep d.cutoff d.period d.level).eval U)⁻¹ •
    (Poly.pass (q.read b (Currency.gain x) U)*(O.residual.leaf b).density U -
      gust R.family.path d.cutoff d.period (d₀.level+1) (WilsonReportingPrescribedOldHistory.calendar R period
        (WilsonReportingPrescribedOldRawForecast.raw R hG u J₀ d₀ Q o μ ks t₀)) d.level live U)

/-- Every earlier gauge and every bounded measurable signed spectator are
tested under the same old Wilson conditional. -/
def Earlier {n per j : ℕ} (_jN : j ≤ n) (f : Config G (R.family.side j per) → ℂ) (B : ℝ) : Prop :=
  ∀ {k : ℕ} (lower : k ≤ j), ∀ H : Config G (R.family.side j per) → ℂ, Envelope H →
    ∀ W : Config G (R.family.side k per),
      ‖actualTransport R.family (N:=n) (fun U => H U*f U) lower W‖ ≤
        B*actualTransport R.family (N:=n) (fun U => ‖H U‖) lower W

private theorem dominated (C : Family G) (hC : C.Makes) {N per l m : ℕ} (hm : m≤ N) {w : Config G (C.side m per) → ℝ}
    (hw : Envelope w) (f : Config G (C.side m per) → ℂ) {B : ℝ}
    (hf : ∀U,‖f U‖≤ B*w U) (hl : l ≤ m) (V : Config G (C.side l per)) :
    ‖actualTransport C (N:=N) f hl V‖≤ B*actualTransport C (N:=N) w hl V := by
  induction hl using Nat.decreasingInduction with
  | self => simpa only [actualTransport_base C hC hm] using hf V
  | of_succ j hj ih =>
    rw [actualTransport_step C hC hm f hj,actualTransport_step C hC hm w hj]
    unfold actualAverage
    rw [←integral_const_mul]
    obtain ⟨b,hb⟩:=hw.cost
    have hi:=actualTransport_weighted_integrable C hC hm hw.meas.aestronglyMeasurable hb hj
    apply norm_integral_le_of_norm_le ((ActualWilsonAbsoluteTransport.slice C hi V).const_mul B)
    exact ae_of_all _ fun U=>by
      rw [norm_smul,Real.norm_of_nonneg (actualConditionalDensity_nonneg C hC (hj.trans_le hm) V U),smul_eq_mul]
      exact (mul_le_mul_of_nonneg_left (ih U) (actualConditionalDensity_nonneg C hC (hj.trans_le hm) V U)).trans_eq (by ring)

theorem tested {n per j : ℕ} (jN : j ≤ n) (f : Config G (R.family.side j per) → ℂ) {B : ℝ}
    (price : ∀U, ‖f U‖≤B) : Earlier R jN f B := by
  intro k lower H envelope W
  have measured : Envelope (fun U=>‖H U‖) := by
    obtain ⟨C,hC⟩ := envelope.cost
    exact ⟨envelope.meas.norm,C, fun U=> by simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hC U⟩
  refine dominated R.family R.makes jN measured _ (fun U=>?_) lower W
  rw [norm_mul,mul_comm B]
  exact mul_le_mul_of_nonneg_left (price U) (norm_nonneg _)

end YM.Integration.WilsonReportingPrescribedOldRawReading
