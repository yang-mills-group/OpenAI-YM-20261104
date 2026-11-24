import YM.Integration.ActualSelectedVacuumBeta
import YM.Integration.ActualRequestedKineticPayment

/-! The exact affine-reset beta is calibrated at the requested output norm.
Its arbitrary mesh accuracy pays the complete regular and global-hit tariff.
The calibration is carried on the original selected output, and its amount
is the literal full clipped kinetic discrepancy on every field. No Coin,
threshold inverse, forced fusion or omitted soft logarithm is introduced. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualSelectedResetCalibration
open Function Filter Lattice Wilson WilsonStartup RG Marker
open PhysicalNext.Repeat.Legato PhysicalNext.ThroughLaunch
open IterationFour IterationFour.Vacuum
open AnalyticBridge VerifiedReset Collection Averaging
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open ActualRunAdmissionScales OriginalRunConstruction
open scoped Topology Classical BigOperators

variable {G : Gauge}

private theorem mesh_weight (C : Family G) (t : Real) :
    ∃ q : Nat, ∀ m : Nat, (Kinetic.price C m^q)⁻¹ ≤
      Currency.weight C.path.levels t m := by
  obtain ⟨q, hq⟩ := exists_nat_ge t
  refine ⟨q, fun m => ?_⟩
  let A := C.path.levels
  have hb := WardBin.hot A m
  have hp : Currency.B A m ≤ Kinetic.price C m :=
    (show Currency.B A m ≤ 2 * Currency.B A m by linarith).trans
      (Kinetic.two_hat_le C m)
  have hq2 : t ≤ 2 * (q : Real) := by
    linarith [Nat.cast_nonneg (α := Real) q]
  calc
    _ ≤ ((Currency.B A m)^q)⁻¹ :=
      inv_anti₀ (pow_pos hb q) (pow_le_pow_left₀ hb.le hp q)
    _ = Currency.weight A (2 * (q : Real)) m := by
      unfold Currency.weight
      rw [show Currency.hat A m = Currency.gain (Currency.B A m) from rfl,
        Currency.rpGain _ hb,
        show -(2 * (q : Real)) / 2 = -(q : Real) by ring,
        Real.rpow_neg hb.le, Real.rpow_natCast]
    _ ≤ Currency.weight A t m := Currency.weight_le A m hq2

private theorem requested_eq (run : Run G) {V : Type} {J : Request V}
    (A : NumericSchedule run.family J) (m : Nat) :
    A.outputNorm m = requestedBudget run.family.path.levels m
      J.outputFieldOrder J.outputDistanceOrder J.outputSupport
      J.field_minimum J.distance_minimum J.output_support_pos :=
  ActualRepeatedNorm.norm_unique run.family J.outputFieldOrder
    J.outputDistanceOrder J.outputSupport J.field_minimum J.distance_minimum
    J.output_support_pos m (A.outputNorm m) (A.output_norm m)

private theorem path_bounds (run : Run G) {V : Type} [DecidableEq V] {Gamma : Census V}
    (datum : LocalFormal.Datum run.family Gamma) :
    (run.family.path.rep datum.cutoff datum.period datum.level).path.Bounds
      (run.family.path.levels.params datum.level).clip
      (run.family.path.levels.params datum.level).width
      (run.family.path.levels.params datum.level).paths
      (run.family.path.levels.clock.loopCap datum.level) := by
  have hs : run.family.path.Conv datum.cutoff datum.period datum.level :=
    run.makes.wilson.represents datum.cutoff datum.period datum.level datum.below.le
  rw [← hs.clip]
  exact hs.good.paths

private theorem decent (run : Run G) {V : Type} {J : Request V}
    (A : NumericSchedule run.family J) (m : Nat) :
    Decent (run.family.path.levels.params m).clip (A.outputNorm m) := by
  have h := (ActualRunRequestedWidth.native_geometry run m).1
  exact ⟨h.direct, by simpa only [(A.output_norm m).block] using h.radius,
    by simpa only [(A.output_norm m).block, (A.output_norm m).threshold] using h.cut⟩

private def widen {n : Side} {Q : Rep G n} {p : BudgetPoint}
    {eta eta' : Real} (C : CalibrationPresentation Q p eta) (h : eta ≤ eta') :
    CalibrationPresentation Q p eta' :=
  { C with
    size_nonnegative := C.size_nonnegative.trans h
    regular_total x := ⟨(C.regular_total x).1, (C.regular_total x).2.1,
      (C.regular_total x).2.2.trans h⟩
    full_hit x := ⟨(C.full_hit x).1, (C.full_hit x).2.1,
      (C.full_hit x).2.2.trans h⟩ }

/-- Every fixed target order is paid by the actual reset-beta mesh estimate,
including the global-hit part of the kinetic calibration. -/
theorem price (run : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached run)
    (hReadout : RG05Preconstruction.ReadoutPurchase run.b)
    (hprofile : WithStage run.metals.p originalOrders)
    {V : Type} [Fintype V] [DecidableEq V] {Gamma : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule run.family J) (K : NumericPrices A)
    (t kappa : Real) (hkappa : 0 < kappa) :
    ∀ᶠ m : Nat in atTop,
      ∀ (datum : LocalFormal.Datum run.family Gamma), datum.level = m →
      ∀ (Y : YM.Comparison.RG02.Bulk.Chain run.family.path)
        (F : AnalyticInput J A datum) (eta_w : Real)
        (I : FullPreparedInputAt F eta_w) (M : AnalyticOutput caps Y K F)
        (S : Retained.Chosen K I M),
      eta_w ≤ (Currency.g run.family datum.cutoff datum.period (datum.level+1))^2 →
      I.carrier.rep.eval =
        (run.family.path.rep datum.cutoff datum.period (datum.level+1)).eval →
      NativeKineticCalibration.price G
        (run.family.path.levels.params datum.level).clip (A.outputNorm datum.level)
        (run.family.path.levels.params datum.level).width
        (run.family.path.levels.params datum.level).paths
        (M.plan.predict datum.level + delta (S.vacuum.listing.read S.vacuum.source) -
          run.family.path.β datum.cutoff datum.period datum.level) ≤
        kappa * Currency.weight run.family.path.levels t datum.level := by
  obtain ⟨q, hq⟩ := mesh_weight run.family (t+1)
  obtain ⟨k, hquotes⟩ :=
    ActualSelectedVacuumBeta.quotes run hG hT hReadout hprofile caps A K
  filter_upwards [
    ActualSelectedVacuumBeta.reset_defect run hG hT hReadout hprofile caps A K q,
    hquotes,
    ActualRequestedKineticPayment.unitCost_weight run.family.path.levels hG
      (ActualRunQLocalAdmission.actual_preMesh run hReadout)
      J.outputFieldOrder J.outputDistanceOrder J.outputSupport
      J.field_minimum J.distance_minimum J.output_support_pos t kappa hkappa]
    with m hreset hgeometry hcost
  intro datum hlevel Y F eta_w I M S hcal hFine
  subst m
  obtain ⟨hw, _hstripe, _hquote⟩ := hgeometry datum rfl Y F eta_w I M S hcal
  have hdelta := (hreset datum rfl Y F eta_w I M S hcal hFine).trans (hq datum.level)
  have hp := NativeKineticCalibration.price_le (path_bounds run datum) hw hdelta
  have hc := hcost (run.family.path.levels.params datum.level).clip
    (decent run A datum.level).direct
  rw [← requested_eq run A datum.level] at hc
  exact hp.trans hc

/-- The paid presentation uses the same selected physical carrier and every
original kinetic row. Widening changes only the three budget proof fields. -/
theorem calibration (run : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached run)
    (hReadout : RG05Preconstruction.ReadoutPurchase run.b)
    (hprofile : WithStage run.metals.p originalOrders)
    {V : Type} [Fintype V] [DecidableEq V] {Gamma : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule run.family J) (K : NumericPrices A)
    (t kappa : Real) (hkappa : 0 < kappa) :
    ∀ᶠ m : Nat in atTop,
      ∀ (datum : LocalFormal.Datum run.family Gamma), datum.level = m →
      ∀ (Y : YM.Comparison.RG02.Bulk.Chain run.family.path)
        (F : AnalyticInput J A datum) (eta_w : Real)
        (I : FullPreparedInputAt F eta_w) (M : AnalyticOutput caps Y K F)
        (S : Retained.Chosen K I M),
      eta_w ≤ (Currency.g run.family datum.cutoff datum.period (datum.level+1))^2 →
      I.carrier.rep.eval =
        (run.family.path.rep datum.cutoff datum.period (datum.level+1)).eval →
      ∃ C : CalibrationPresentation S.output.carrier.rep (A.outputNorm datum.level)
          (kappa * Currency.weight run.family.path.levels t datum.level),
        ∀ U, C.amount U =
          (M.plan.predict datum.level + delta (S.vacuum.listing.read S.vacuum.source) -
            run.family.path.β datum.cutoff datum.period datum.level) *
          Push.BetaTransport.kinetic
            (run.family.path.rep datum.cutoff datum.period datum.level).path
            (run.family.path.levels.params datum.level).clip
            (A.outputNorm datum.level) U := by
  obtain ⟨k, hquotes⟩ :=
    ActualSelectedVacuumBeta.quotes run hG hT hReadout hprofile caps A K
  filter_upwards [price run hG hT hReadout hprofile caps A K t kappa hkappa,
    hquotes] with m hprice hgeometry
  intro datum hlevel Y F eta_w I M S hcal hFine
  subst m
  obtain ⟨hw, _hstripe, _hquote⟩ := hgeometry datum rfl Y F eta_w I M S hcal
  have hthreshold :
      (A.outputNorm datum.level).threshold = S.output.carrier.rep.p.threshold := by
    rw [S.vacuum.representation]
    exact (A.output_norm datum.level).threshold
  let defect := M.plan.predict datum.level +
    delta (S.vacuum.listing.read S.vacuum.source) -
    run.family.path.β datum.cutoff datum.period datum.level
  let C := NativeKineticCalibration.calibration (path_bounds run datum)
    (decent run A datum.level) hw S.output.carrier.rep hthreshold defect
  refine ⟨widen C (hprice datum rfl Y F eta_w I M S hcal hFine), ?_⟩
  intro U
  change C.amount U = _
  exact NativeKineticCalibration.amount (path_bounds run datum)
    (decent run A datum.level) hw S.output.carrier.rep hthreshold defect U

end YM.Integration.ActualSelectedResetCalibration
end
