import YM.Integration.WilsonReportingPrescribedOldUpperForecast
import YM.Integration.WilsonReportingPrescribedOldFirstVacuum
import YM.Integration.WilsonReportingPrescribedOldRawReading
import YM.Integration.WilsonReportingPrescribedOldSites

/-! A genuinely nonbare comparison for the independently specified original
MS source. The same genuine predecessor is issued on all actual fine cells,
restored in the full source normalization and tested on every earlier Wilson
conditional, with a signed correlated spectator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldFirstCourse
open Filter Lattice Wilson RG Source Marker Precision MergeProof.Accent
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 QLocalVacuumOrderRestriction AnalyticBridge.VerifiedReset.Averaging
open WilsonLimitConstruction Pert.Asymptotics ActualRunInterpolatedPackets QLocalMarkedCouplingDifference
open FullQLocal.PreRun.SuccessiveRequests RG3.Script.Picnic QLocalOriginalQHistory
open WilsonReportingPrescribedOldRawReading
open scoped Topology Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] {B : MS.Local.Physical.Deck G}
  (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B)
  (Q : MS.Land.Prescription B) (μ : ℝ) (K₀ : ℕ)
  (J₀ : Request V) (A₀ : NumericSchedule R.family J₀)
local notation "JB" => ActualOriginalQPointSetup.request R u J₀
local notation "AB" => ActualOriginalQInitialInput.schedule R hG u J₀ A₀
local notation "startF" => ActualOriginalQInitialInput.input R hG u J₀ A₀

/-- The chosen radii are those of the original funded successor. The zero-test
kinetic observation is taken on its genuinely issued lower catalogue. -/
def Audited (extra : ℕ) (ord : ∀ k,k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power)
    (cap₀ : Handoff.OutputCapacities) (K₁ : NumericPrices (AB)) (r₀ : ℕ)
    (A : NumericSchedule R.family (nextRequest (JB) cap₀ r₀)) (K : NumericPrices A)
    (caps : Handoff.OutputCapacities) (p r : ℕ) (ε : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ (d₀ : LocalFormal.Datum R.family (Stock.census V)) (date : d₀.level=m+1),
    ∀ (b : ℕ) (fine : b≤d₀.level+1) (parents : V→Site (R.family.side b d₀.period))
      (residues : V→Site (R.family.S.toDepth fine d₀.period).count) (ks : V→ℕ), (∀ i,ks i≤K₀) →
    ∀ (period : (JB).physicalPeriodLower ≤ (R.family.S.period d₀.period).val), d₀.cutoff=d₀.level+1 →
    let sites := fun i=>(R.family.S.toDepth fine d₀.period).assemble (parents i,residues i)
    ∃ first : ActualOriginalQInitialInput.start R hG u J₀ A₀ ord ≤ d₀.level,
    ∃ I₀ : FullPreparedInputAt (startF d₀ Q sites μ ks ord first period) 0,
    Retained.NativeIntake I₀ ∧ I₀.regularPrice=0 ∧ I₀.forcedPrice=0 ∧
    ∀ (M₀ : FundedPhysicalCatalogue.Purchase cap₀ K₁ (startF d₀ Q sites μ ks ord first period))
      (S₀ : FundedRenderedBank.Chosen K₁ I₀ M₀.toCatalogue) (bank : FundedRenderedBank.Canonical S₀)
      (W : Bulk.Colors (Stock.census V) G (R.family.side (m+1) d₀.period))
      (x : Exterior.fieldDir G (R.family.side m d₀.period) 1) (q : ℕ)
      (next : FundedCoverStepPrice.Receipt R M₀ S₀ bank r₀ date A W x q),
      next.analytic.outputRadii = (fun v=>(startF d₀ Q sites μ ks ord first period).outputRadii v/A.radiusLoss m) →
    ∀ (received : FundedCoverFlatStep.Accepted R next),
    let d := ActualNextLocalDatum.descend d₀ date W x
    let J := nextRequest (JB) cap₀ r₀
    ∀ (Y : Bulk.Chain R.family.path) (M : FundedPhysicalCatalogue.Purchase caps K next.analytic),
      FundedCoverKineticMeasurement.Tested R Y next.analytic M hG (fun v=>(0 : (J.tests v).Mood)) →
    ∀ (S : FundedRenderedBank.Chosen K received.input M.toCatalogue) (t : IndependentTests J.tests),
    ∃ t₀ : IndependentTests (JB).tests, HEq (testInclusion J.tests t) (testInclusion _ t₀) ∧
    ∃ live : d.level≤d₀.level+1,
    let Δ := difference R hG u J₀ A₀ caps J A K d next.analytic received.input M S (p+2+extra) r
      d₀ rfl live Q sites μ ks t t₀
    let fee := ε*(regulatorRun R.family d₀.cutoff d₀.period (m+1))^((p:ℝ)+1-J.eta)
    ∀ s : (Stock.census V).Mode, (∀U, ‖(Δ U).part s‖ ≤ fee) ∧
      Earlier R ((Nat.le_succ _).trans d.below) (fun U=>(Δ U).part s) fee

include hG in
theorem original (T : Campaign R) (attached : ActualRunNativeComponentRecipe.Attached R)
    (readout : RG05Preconstruction.ReadoutPurchase R.b) :
    ∃ extra : ℕ, ∀ (J₀ : Request V) (A₀ : NumericSchedule R.family J₀)
      (ord : ∀ k,k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power)
      (cap₀ : Handoff.OutputCapacities) (K₁ : NumericPrices (ActualOriginalQInitialInput.schedule R hG u J₀ A₀))
      (r₀ : ℕ) (A : NumericSchedule R.family (nextRequest (ActualOriginalQPointSetup.request R u J₀) cap₀ r₀))
      (K : NumericPrices A) (caps : Handoff.OutputCapacities) (p r : ℕ), p+2+extra≤J₀.order →
    ∀ {ε : ℝ}, 0<ε → Audited R hG u Q μ K₀ J₀ A₀ extra ord cap₀ K₁ r₀ A K caps p r ε := by
  obtain ⟨extra,quote⟩ := WilsonReportingPrescribedOldUpperForecast.original R hG u Q μ K₀
  refine ⟨extra,?_⟩
  intro J₀ A₀ ord cap₀ K₁ r₀ A K caps p r ready ε ep
  let Jb := ActualOriginalQPointSetup.request R u J₀
  let Ab := ActualOriginalQInitialInput.schedule R hG u J₀ A₀
  let J := nextRequest Jb cap₀ r₀
  have hOrder : p+2+extra≤J.order := ready
  have paid := quote J₀ A₀ attached readout caps J A K (p+2) r (by omega) hOrder (half_pos ep)
  have birth := (tendsto_add_atTop_nat 1).eventually (WilsonReportingPrescribedOldSites.original R hG u J₀ A₀ T ord)
  filter_upwards [paid,birth,WilsonReportingPrescribedOldFirstRadii.eligible R 0,
    WilsonReportingPrescribedOldFirstReceipt.original R hG u J₀ A₀ cap₀ r₀ A,
    WilsonReportingPrescribedOldFirstVacuum.calibrated (Γ:=Stock.census V) R hG attached readout cap₀ Jb Ab K₁ r₀,
    eventually_ge_atTop (ActualOriginalQLayout.referenceLevel R u)]
    with m forecast roots eligible radii calibration reference
  intro d₀ date b fine parents residues ks order period cut
  let sites := fun i=>(R.family.S.toDepth fine d₀.period).assemble (parents i,residues i)
  obtain ⟨first,I₀,intake,carrier,reg,force,source⟩ := roots d₀ date b fine parents residues Q μ ks period cut
  refine ⟨first,I₀,intake,reg,force,?_⟩
  intro M₀ S₀ bank W x q next chosen received
  dsimp only
  intro Y M contact S t
  let d := ActualNextLocalDatum.descend d₀ date W x
  have cutoff : d.cutoff=m+1+1 := by change d₀.cutoff=_; omega
  have liveN : m<d₀.cutoff := by omega
  have scope : ActualOriginalQLayout.referenceLevel R u ≤ d₀.level+1 := by omega
  have old := QLocalOriginalQHistory.issued R hG u J₀ A₀ d₀ Q sites μ ks source received
  have regular := WilsonReportingPrescribedOldFirstVacuum.earlier R received (congrArg (fun y=>y.eval) carrier)
  obtain ⟨t₀,tag,live,estimate⟩ := forecast (Nat.le_succ m) eligible d rfl cutoff Y next.analytic _ received.input M
    contact S (calibration _ _ liveN period) regular d₀ scope sites ks order old t
  refine ⟨t₀,tag,live,?_⟩
  intro s
  let Δ := difference R hG u J₀ A₀ caps J A K d next.analytic received.input M S (p+2+extra) r
    d₀ rfl live Q sites μ ks t t₀
  let g := regulatorRun R.family d₀.cutoff d₀.period (m+1)
  let v := Poly.toll (fun i=>next.analytic.outputRadii i/next.analytic.kernelCosts i) s
  let e := (p:ℝ)+1-J.eta
  have positive : 0<v := Poly.worth (fun i=>div_pos (next.analytic.output_radius_positive i) (next.analytic.kernel_positive i)) s
  have gp : 0<g := Currency.g_pos R.makes _ _ _ liveN
  have registered := (radii d₀ date Q sites μ ks ord first period K₁ I₀ M₀ S₀ bank W x q next chosen s).2
  have paid : ∀U, ‖(Δ U).part s‖≤ε*g^e := by
    intro U
    have receipt : v*‖(Δ U).part s‖ ≤ (ε/2)*g^((((p+2:ℕ):ℝ)+1)-J.eta) := estimate U s
    have index : (((p+2:ℕ):ℝ)+1)-J.eta = e+2 := by dsimp only [e]; push_cast; ring
    rw [index,Real.rpow_add gp,Real.rpow_two] at receipt
    apply (le_of_mul_le_mul_left _ positive)
    calc
      _ ≤ _ := receipt
      _ ≤ ((ε/2)*g^e)*(2*v) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left registered (Real.rpow_nonneg gp.le _)) (half_pos ep).le
      _ = v*(ε*g^e) := by ring
  exact ⟨paid, WilsonReportingPrescribedOldRawReading.tested R ((Nat.le_succ _).trans d.below) _ paid⟩

end YM.Integration.WilsonReportingPrescribedOldFirstCourse
