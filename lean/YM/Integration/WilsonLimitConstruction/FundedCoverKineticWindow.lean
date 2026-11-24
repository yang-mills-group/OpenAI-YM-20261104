import YM.Integration.WilsonLimitConstruction.FundedCoverKineticQuote
import YM.Integration.WilsonLimitConstruction.FundedCanonicalCalibration
import YM.Integration.ActualSelectedResetCalibration

/-! One true sized upper envelope of every actual signed reset price on the
fixed native run. The envelope is independent of all future model choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedCoverKineticWindow
open Function Filter Lattice Wilson WilsonStartup RG Marker
open PhysicalNext.Repeat.Legato PhysicalNext.ThroughLaunch
open IterationFour IterationFour.Vacuum
open AnalyticBridge VerifiedReset Collection Averaging
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open ActualRunAdmissionScales OriginalRunConstruction
open FundedPhysicalCatalogue FundedCoverKineticMeasurement
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

/-- Every fixed target order is paid by the actual reset-beta mesh estimate,
including the global-hit part of the kinetic calibration. -/
theorem price (run : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached run)
    (hReadout : RG05Preconstruction.ReadoutPurchase run.b)
    {V : Type} [Fintype V] [DecidableEq V] {Gamma : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule run.family J) (K : NumericPrices A)
    (t kappa : Real) (hkappa : 0 < kappa) :
    ∀ᶠ m : Nat in atTop,
      ∀ (datum : LocalFormal.Datum run.family Gamma), datum.level = m →
      ∀ (Y : YM.Comparison.RG02.Bulk.Chain run.family.path)
        (F : AnalyticInput J A datum) (eta_w : Real)
        (I : FullPreparedInputAt F eta_w) (M : FundedPhysicalCatalogue.Purchase caps K F)
        (_contact : Tested run Y F M hG (fun v => (0 : (J.tests v).Mood))) (S : FundedRenderedBank.Chosen K I M.toCatalogue),
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
    FundedCoverKineticQuote.quotes run hG hT hReadout caps A K
  filter_upwards [
    FundedCoverKineticQuote.reset_defect run hG hT hReadout caps A K q,
    hquotes,
    ActualRequestedKineticPayment.unitCost_weight run.family.path.levels hG
      (ActualRunQLocalAdmission.actual_preMesh run hReadout)
      J.outputFieldOrder J.outputDistanceOrder J.outputSupport
      J.field_minimum J.distance_minimum J.output_support_pos t kappa hkappa]
    with m hreset hgeometry hcost
  intro datum hlevel Y F eta_w I M contact S hcal hFine
  subst m
  obtain ⟨hw, _hstripe, _hquote⟩ := hgeometry datum rfl Y F eta_w I M contact S hcal
  have hdelta := (hreset datum rfl Y F eta_w I M contact S hcal hFine).trans (hq datum.level)
  have hp := NativeKineticCalibration.price_le (FundedCanonicalInputPayload.path_bounds run (datum := datum)) hw hdelta
  have hc := hcost (run.family.path.levels.params datum.level).clip
    (FundedCanonicalInputPayload.decent run (A := A) (datum := datum)).direct
  rw [← requested_eq run A datum.level] at hc
  exact hp.trans hc

variable {V : Type} [Fintype V] [DecidableEq V] {Γ : Census V} {J : Request V}
    (R : Run G) (caps : Handoff.OutputCapacities) (A : NumericSchedule R.family J)
    (K : NumericPrices A)

/-- Only the physical inputs actually eligible to enter the reset are billed. -/
structure Sample (N p m : ℕ) where
  datum : LocalFormal.Datum R.family Γ
  cutoff : datum.cutoff = N
  period : datum.period = p
  level : datum.level = m
  chain : Comparison.RG02.Bulk.Chain R.family.path
  analytic : AnalyticInput J A datum
  eta : ℝ
  input : FullPreparedInputAt analytic eta
  model : FundedPhysicalCatalogue.Purchase caps K analytic
  contact (hG : G.Simple) : Tested R chain analytic model hG (fun v => (0 : (J.tests v).Mood))
  chosen : FundedRenderedBank.Chosen K input model.toCatalogue
  canonical : FundedRenderedBank.Canonical chosen
  small : eta ≤ (Currency.g R.family datum.cutoff datum.period (datum.level+1))^2
  fine : input.carrier.rep.eval = (R.family.path.rep datum.cutoff datum.period (datum.level+1)).eval

def bill {N p m : ℕ} (s : Sample R caps A K (Γ := Γ) N p m) : ℝ :=
  FundedCanonicalCalibration.charge R s.canonical (A.outputNorm s.datum.level)

def values (N p m : ℕ) : Set ℝ :=
  insert 0 (Set.range (bill R caps A K (Γ := Γ) (N := N) (p := p) (m := m)))

def next (N p m : ℕ) : ℝ :=
  if m+1 < N then max 0 (sSup (values R caps A K (Γ := Γ) N p (m+1))) else 0

private theorem upper {N p m : ℕ} {a : ℝ} (ha : 0≤a)
    (h : ∀ s : Sample R caps A K (Γ := Γ) N p m, bill R caps A K s ≤ a) :
    ∀ x ∈ values R caps A K (Γ := Γ) N p m, x ≤ a := by
  rintro x (rfl | ⟨s,rfl⟩)
  · exact ha
  · exact h s

theorem power (hG : G.Simple) (hR : ActualRunNativeComponentRecipe.Attached R)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (q : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ N p, ∀ s : Sample R caps A K (Γ := Γ) N p m,
      bill R caps A K s ≤ (Currency.g R.family N p m)^q := by
  have hc : 0<((2:ℝ)^q)⁻¹ := inv_pos.mpr (pow_pos zero_lt_two q)
  filter_upwards [price R hG hR hReadout caps A K (q:ℝ) _ hc (Gamma := Γ)]
    with m paid
  rintro N p ⟨d, hN, hp, hm, Y, F, η, I, M, contact, S, P, hsmall, hfine⟩
  subst N
  subst p
  subst m
  have h := paid d rfl Y F η I M (contact hG) S hsmall hfine
  have hbill : FundedCanonicalCalibration.charge R P (A.outputNorm d.level) ≤
      ((2:ℝ)^q)⁻¹ * Currency.weight R.family.path.levels (q:ℝ) d.level := by
    unfold FundedCanonicalCalibration.charge FundedCanonicalCalibration.defect
    rw [(FundedCanonicalCalibration.parameters R P).1]
    exact h
  have hw : Currency.weight R.family.path.levels (q:ℝ) d.level ≤
      (2:ℝ)^q*(Currency.g R.family d.cutoff d.period d.level)^q := by
    simpa only [Real.rpow_natCast] using
      (Currency.g_weight (C := R.family) (q := d.period) R.makes d.below.le (q:ℝ)
        (Nat.cast_nonneg q)).1
  exact hbill.trans ((mul_le_mul_of_nonneg_left hw hc.le).trans_eq
    (by rw [← mul_assoc,inv_mul_cancel₀ (pow_ne_zero q (by norm_num : (2:ℝ)≠0)),one_mul]))

theorem dominates (hG : G.Simple) (hR : ActualRunNativeComponentRecipe.Attached R)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    :
    ∀ᶠ m : ℕ in atTop, ∀ N p, ∀ s : Sample R caps A K (Γ := Γ) N p (m+1),
      bill R caps A K s ≤ next R caps A K (Γ := Γ) N p m := by
  obtain ⟨first,h⟩ := Filter.eventually_atTop.1
    (power R caps A K (Γ := Γ) hG hR hReadout 0)
  refine Filter.eventually_atTop.2 ⟨first,?_⟩
  intro m hm N p s
  have hunit := h (m+1) (hm.trans (Nat.le_succ m)) N p
  simp only [pow_zero] at hunit
  have ub : BddAbove (values R caps A K (Γ := Γ) N p (m+1)) :=
    ⟨1,upper R caps A K (Γ := Γ) zero_le_one hunit⟩
  have hlt : m+1 < N := by simpa only [s.level,s.cutoff] using s.datum.below
  rw [next,if_pos hlt]
  exact (le_csSup ub (Or.inr ⟨s,rfl⟩)).trans (le_max_right _ _)

theorem uniformly_flat (hG : G.Simple) (hR : ActualRunNativeComponentRecipe.Attached R)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (J' : Request V) :
    Retained.UniformlyFlat (C := R.family) J' (next R caps A K (Γ := Γ)) := by
  constructor
  · intro N p m _ _
    unfold next
    split
    · exact le_max_left _ _
    exact le_rfl
  intro q
  obtain ⟨first,h⟩ := Filter.eventually_atTop.1
    (power R caps A K (Γ := Γ) hG hR hReadout q)
  refine ⟨first,?_⟩
  intro N p m hm hN _
  have hzero : 0 ≤ (Currency.g R.family N p (m+1))^q :=
    pow_nonneg (Currency.g_pos R.makes N p (m+1) (Nat.succ_le_of_lt hN)).le q
  unfold next
  split
  · apply max_le hzero
    exact csSup_le ⟨0,Or.inl rfl⟩ (upper R caps A K (Γ := Γ) hzero
      (h (m+1) (hm.trans (Nat.le_succ m)) N p))
  exact hzero

theorem initial_zero (p m : ℕ) : next R caps A K (Γ := Γ) (m+1) p m = 0 := by
  simp only [next,lt_self_iff_false,if_false]

end YM.Integration.WilsonLimitConstruction.FundedCoverKineticWindow
end
