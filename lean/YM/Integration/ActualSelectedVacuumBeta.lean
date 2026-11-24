import YM.Integration.ActualSelectedVacuumGerm
import YM.Integration.ActualRunKineticGerm
import YM.Integration.ActualCappedRegularPayment
import YM.Integration.FullQLocalNumericVacuumRateBound
import YM.Integration.SelectedPlanPredictedStripe

/-! Sharp same-Run beta control from the complete selected quiet source.
All requested geometry, original-list invoice and kinetic Quotes are derived
on one tail. Only the actual incoming vacuum attachment and its order-two
calibration-domain condition remain input duties. No Coin or beta equality
is assumed. The exact source rate and mesh error remain separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualSelectedVacuumBeta
open Function Filter Lattice Wilson WilsonStartup RG Marker
open PhysicalNext.Repeat.Legato PhysicalNext.ThroughLaunch
open IterationFour IterationFour.Vacuum
open AnalyticBridge VerifiedReset Collection
open AnalyticBridge.VerifiedReset.Averaging
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open ActualRunAdmissionScales OriginalRunConstruction
open MatchingLedger.Compass.Income Extra.Iteration
open ActualSelectedVacuumGerm ZeroAwareIntrinsicRenderInvoice
open scoped Topology Classical BigOperators

variable {G : Gauge}

private theorem requested_eq (run : Run G) {V : Type} {J : Request V}
    (A : NumericSchedule run.family J) (m : Nat) :
    A.outputNorm m = requestedBudget run.family.path.levels m
      J.outputFieldOrder J.outputDistanceOrder J.outputSupport
      J.field_minimum J.distance_minimum J.output_support_pos :=
  ActualRepeatedNorm.norm_unique run.family J.outputFieldOrder
    J.outputDistanceOrder J.outputSupport J.field_minimum J.distance_minimum
    J.output_support_pos m (A.outputNorm m) (A.output_norm m)

private theorem cost_le_price (run : Run G) (hG : G.Simple)
    {V : Type} {J : Request V} (A : NumericSchedule run.family J) :
    ∀ᶠ m : Nat in atTop,
      A.admittedCost m ≤ 2 * Kinetic.price run.family m := by
  obtain ⟨first, hcost⟩ := A.cost_subpower 2 (by norm_num)
  filter_upwards [eventually_ge_atTop first,
    ActualRunAdjacentHatBeta.three_halves run hG] with m hm hnext
  let g := Pert.Asymptotics.regulatorRun run.family (m+1) 0 (m+1)
  let beta := run.family.path.β (m+1) 0 (m+1)
  have hg : 0 < g := Weather.runs_pos run.family run.makes le_rfl 0
  have hepoch : beta * g^2 = 1 := Weather.epoch run.family run.makes le_rfl 0
  have hi : (g^2)⁻¹ = beta := by
    calc
      _ = (beta * g^2) * (g^2)⁻¹ := by rw [hepoch, one_mul]
      _ = beta := by
        rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hg.ne'), mul_one]
  have hc := hcost m hm (m+1) 0 (Nat.lt_succ_self m)
  change A.admittedCost m ≤ g ^ (-(2 : Real)) at hc
  rw [Real.rpow_neg hg.le, Real.rpow_two, hi] at hc
  have hb := (run.makes.wilson.represents (m+1) 0 (m+1) le_rfl).band.2
  have hp := Kinetic.two_hat_le run.family m
  have hpos := WardBin.hot run.family.path.levels m
  change beta ≤ 2 * run.family.path.levels.clock.hatBeta (m+1) at hb
  change run.family.path.levels.clock.hatBeta (m+1) ≤
    (3/2 : Real) * run.family.path.levels.clock.hatBeta m at hnext
  linarith

private theorem gain_le_one {b : Real} (hb : 1 ≤ b) : Currency.gain b ≤ 1 := by
  have hs : 1 ≤ Real.sqrt b := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hb
  exact inv_le_one_of_one_le₀ hs

/-- One event derives the full requested-norm kinetic Quotes. The polynomial
quote exponent is fixed before all cutoffs, periods and selected data. -/
theorem quotes (run : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached run)
    (hReadout : RG05Preconstruction.ReadoutPurchase run.b)
    (hprofile : WithStage run.metals.p originalOrders)
    {V : Type} [Fintype V] [DecidableEq V] {Gamma : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule run.family J) (K : NumericPrices A) :
    ∃ k : Nat, ∀ᶠ m : Nat in atTop,
      ∀ (datum : LocalFormal.Datum run.family Gamma), datum.level = m →
      ∀ (Y : YM.Comparison.RG02.Bulk.Chain run.family.path)
        (F : AnalyticInput J A datum) (eta_w : Real)
        (I : FullPreparedInputAt F eta_w) (M : AnalyticOutput caps Y K F)
        (_S : Retained.Chosen K I M),
      eta_w ≤ (Currency.g run.family datum.cutoff datum.period (datum.level+1))^2 →
      Geo.Width (A.outputNorm datum.level)
          (run.family.path.levels.params datum.level).clip
          (run.family.path.levels.params datum.level).width ∧
      M.plan.predict datum.level ∈
          Currency.stripe (Currency.B run.family.path.levels datum.level) ∧
      Pert.Kinetic.Quotes (A.outputNorm datum.level)
        (run.family.path.levels.params datum.level).width
        (run.family.path.levels.params datum.level).paths
        (run.family.path.levels.clock.loopCap datum.level)
        (regularPrice run I M) (Kinetic.price run.family datum.level ^ (k+1)) := by
  obtain ⟨C, hC, D, hbills⟩ :=
    SelectedPlanIntrinsicRenderCost.selected_bounds run hG (R := Gamma) caps A K
  let H0 := (K.vacuumConstant + 1) * J.inheritedConstant + 2
  have hH0 : 0 ≤ H0 := by
    have := K.vacuum_constant_nonnegative
    have := J.inherited_constant_nonnegative
    dsimp only [H0]
    positivity
  have hregular := ActualCappedRegularPayment.regular_price run hG hReadout
    J.outputFieldOrder J.outputDistanceOrder J.outputSupport
    J.field_minimum J.distance_minimum J.output_support_pos H0 hH0
  have hwidth := ActualRunRequestedWidth.eventually_geometry run hprofile
    J.outputFieldOrder J.outputDistanceOrder J.outputSupport
    J.field_minimum J.distance_minimum J.output_support_pos
  have hlarge := Next.Rank.Station.hat_rate run.family.path.levels hG
  refine ⟨D+1, ?_⟩
  filter_upwards [hbills, hregular, hwidth,
    K.eventually_vacuumRate_bounded hG run.makes,
    SelectedPlanPredictedStripe.predicted run hG hT (R := Gamma) caps A K,
    cost_le_price run hG A, Kinetic.quote_eventually run.family hG,
    hlarge.eventually_ge_atTop (C * 2^D),
    hlarge.eventually_ge_atTop J.outputSupport⁻¹]
    with m hbill hreg hw hrate hstripe hcost hn hlargeC hlargeS
  intro datum hlevel Y F eta_w I M S hcal
  subst m
  have hW : Geo.Width (A.outputNorm datum.level)
      (run.family.path.levels.params datum.level).clip
      (run.family.path.levels.params datum.level).width := by
    rw [requested_eq run A datum.level]
    exact hw.2
  have hS := hstripe datum rfl Y F M
  have hLaw := ActualSelectedVacuumGerm.lawful run S hG hW hS
  have hsource : 0 ≤ sourcePrice run I K := S.vacuum.estimate.H_nonneg
  have hsourceBound : sourcePrice run I K ≤ H0 :=
    hrate datum.cutoff datum.period datum.below I.inherited eta_w
      I.inherited_nonnegative I.inherited_bound hcal
  have hregularBound :
      CappedRegularReset.regularNeed G (A.outputNorm datum.level)
        (run.family.path.levels.params datum.level).clip
        (run.family.path.levels.params datum.level).width
        (run.family.path.levels.params datum.level).paths 0
        (sourcePrice run I K) ≤ Kinetic.price run.family datum.level := by
    rw [requested_eq run A datum.level]
    exact hreg _ _ _ hLaw.paths hsource hsourceBound
  let P := Kinetic.price run.family datum.level
  let b := Currency.B run.family.path.levels datum.level
  have hP : 1 ≤ P := hn.pos
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hhat : 0 < b := WardBin.hot run.family.path.levels datum.level
  have hhatOne : 1 ≤ b := (run.family.path.levels.fits.delayed datum.level).le
  have hhatPrice : b ≤ P := by
    have hh := Kinetic.two_hat_le run.family datum.level
    change 2*b ≤ P at hh
    linarith
  have hP2 : 2 ≤ P := by
    have hh := Kinetic.two_hat_le run.family datum.level
    change 2*b ≤ P at hh
    linarith
  have hcoefficient : C * 2^D ≤ P := hlargeC.trans hhatPrice
  have hsupport : J.outputSupport⁻¹ ≤ P := hlargeS.trans hhatPrice
  have hW0 := A.admitted_cost_nonnegative datum.level
  have hgain0 : 0 ≤ Currency.gain b := by
    change 0 ≤ (Real.sqrt b)⁻¹
    positivity
  have hunit := (hbill datum rfl Y F M).1
  have hunitBound :
      Render.unitBill
        (repriceLayers (ZeroAwareCappedRenderInvoice.credit M.vacuum.packets)
          (M.plan.layers datum.level)) b ≤ P^(D+1) := by
    calc
      _ ≤ C * A.admittedCost datum.level^D * Currency.gain b^3 := hunit
      _ ≤ C * A.admittedCost datum.level^D :=
        mul_le_of_le_one_right (mul_nonneg hC.le (pow_nonneg hW0 D))
          (pow_le_one₀ hgain0 (gain_le_one hhatOne))
      _ ≤ C * (2*P)^D :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW0 hcost D) hC.le
      _ = (C * 2^D) * P^D := by rw [mul_pow]; ring
      _ ≤ P * P^D := mul_le_mul_of_nonneg_right hcoefficient (pow_nonneg hP0 D)
      _ = P^(D+1) := by rw [pow_succ]; ring
  have hPd : P ≤ P^(D+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hP (show 1 ≤ D+1 by omega)
  have htotal : regularPrice run I M ≤ P^(D+2) := by
    calc
      _ ≤ P + P^(D+1) := add_le_add hregularBound hunitBound
      _ ≤ 2 * P^(D+1) := by linarith
      _ ≤ P * P^(D+1) :=
        mul_le_mul_of_nonneg_right hP2 (pow_nonneg hP0 (D+1))
      _ = P^(D+2) := by rw [show D+2 = (D+1)+1 by omega, pow_succ P (D+1)]; ring
  obtain ⟨v, hv, hsum⟩ := hLaw.labels.boundE
  have htotal0 : 0 ≤ regularPrice run I M :=
    Cost.nonneg (hsum (0 : Site (run.family.side datum.level datum.period)))
  have hpower : P ≤ P^(D+2) := by
    simpa only [pow_one] using pow_le_pow_right₀ hP (show 1 ≤ D+2 by omega)
  refine ⟨hW, hS, ?_⟩
  refine ⟨hn.pos.trans hpower, hn.jump, hn.width.trans hpower,
    hn.paths.trans hpower, hn.loop.trans hpower, htotal, htotal0, ?_, ?_, ?_⟩
  · rw [(A.output_norm datum.level).block]
    exact hn.cover.trans hpower
  · rw [(A.output_norm datum.level).reserve]
    exact hsupport.trans hpower
  · rw [(A.output_norm datum.level).threshold]
    exact hn.inv_field.trans hpower

/-- The predictor defect is paid by the exact quiet-source rate and an
arbitrary inverse-power mesh error. No threshold inverse is introduced. -/
theorem scaled_defect (run : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached run)
    (hReadout : RG05Preconstruction.ReadoutPurchase run.b)
    (hprofile : WithStage run.metals.p originalOrders)
    {V : Type} [Fintype V] [DecidableEq V] {Gamma : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule run.family J) (K : NumericPrices A) (q : Nat) :
    ∀ᶠ m : Nat in atTop,
      ∀ (datum : LocalFormal.Datum run.family Gamma), datum.level = m →
      ∀ (Y : YM.Comparison.RG02.Bulk.Chain run.family.path)
        (F : AnalyticInput J A datum) (eta_w : Real)
        (I : FullPreparedInputAt F eta_w) (M : AnalyticOutput caps Y K F)
        (_S : Retained.Chosen K I M),
      eta_w ≤ (Currency.g run.family datum.cutoff datum.period (datum.level+1))^2 →
      I.carrier.rep.eval =
        (run.family.path.rep datum.cutoff datum.period (datum.level+1)).eval →
      (A.outputNorm datum.level).threshold^2 *
          |M.plan.predict datum.level -
            run.family.path.β datum.cutoff datum.period datum.level| ≤
        sourcePrice run I K + (A.outputNorm datum.level).threshold^2 *
          (Kinetic.price run.family datum.level^q)⁻¹ := by
  obtain ⟨k, hquotes⟩ := quotes (Gamma := Gamma) run hG hT hReadout hprofile caps A K
  filter_upwards [hquotes, ActualRunKineticGerm.rigidity run hG k q]
    with m hm hr
  intro datum hlevel Y F eta_w I M S hcal hFine
  subst m
  obtain ⟨hw, hstripe, hquote⟩ := hm datum rfl Y F eta_w I M S hcal
  have hgerm := ActualSelectedVacuumGerm.kinetic_germ run S hG hw hFine
  have hLaw := ActualSelectedVacuumGerm.lawful run S hG hw hstripe
  have hbeta := hr datum.cutoff datum.period datum.below.le (shell run S) hgerm
    (run.family.path.levels.params datum.level).width
    (run.family.path.levels.params datum.level).paths
    (run.family.path.levels.clock.loopCap datum.level)
    (regularPrice run I M) (run.family.path.levels.clock.forcedAllowance datum.level)
    hLaw hquote
  rw [ActualSelectedVacuumGerm.beta] at hbeta
  let deltaSource := delta (S.vacuum.listing.read S.vacuum.source)
  let pred := M.plan.predict datum.level
  let actual := run.family.path.β datum.cutoff datum.period datum.level
  let t := (A.outputNorm datum.level).threshold
  have hdelta : t^2 * |deltaSource| ≤ sourcePrice run I K :=
    delta_bound hG S.vacuum.estimate.projects
  have htriangle : |pred-actual| ≤ |pred+deltaSource-actual| + |deltaSource| := by
    calc
      _ = |(pred+deltaSource-actual) + (-deltaSource)| := by congr 1; ring
      _ ≤ _ := by simpa only [abs_neg] using
        abs_add_le (pred+deltaSource-actual) (-deltaSource)
  calc
    _ ≤ t^2 * (|pred+deltaSource-actual| + |deltaSource|) :=
      mul_le_mul_of_nonneg_left htriangle (sq_nonneg t)
    _ = t^2 * |pred+deltaSource-actual| + t^2 * |deltaSource| := by ring
    _ ≤ t^2 * (Kinetic.price run.family datum.level^q)⁻¹ + sourcePrice run I K :=
      add_le_add (mul_le_mul_of_nonneg_left hbeta (sq_nonneg t)) hdelta
    _ = _ := by ring

/-- The affine-reset beta itself has only the arbitrary mesh error.
The extracted source coefficient remains explicit, not charged a second time
as part of this kinetic discrepancy. -/
theorem reset_defect (run : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached run)
    (hReadout : RG05Preconstruction.ReadoutPurchase run.b)
    (hprofile : WithStage run.metals.p originalOrders)
    {V : Type} [Fintype V] [DecidableEq V] {Gamma : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule run.family J) (K : NumericPrices A) (q : Nat) :
    ∀ᶠ m : Nat in atTop,
      ∀ (datum : LocalFormal.Datum run.family Gamma), datum.level = m →
      ∀ (Y : YM.Comparison.RG02.Bulk.Chain run.family.path)
        (F : AnalyticInput J A datum) (eta_w : Real)
        (I : FullPreparedInputAt F eta_w) (M : AnalyticOutput caps Y K F)
        (S : Retained.Chosen K I M),
      eta_w ≤ (Currency.g run.family datum.cutoff datum.period (datum.level+1))^2 →
      I.carrier.rep.eval =
        (run.family.path.rep datum.cutoff datum.period (datum.level+1)).eval →
      |M.plan.predict datum.level +
          delta (S.vacuum.listing.read S.vacuum.source) -
          run.family.path.β datum.cutoff datum.period datum.level| ≤
        (Kinetic.price run.family datum.level^q)⁻¹ := by
  obtain ⟨k, hquotes⟩ := quotes (Gamma := Gamma) run hG hT hReadout hprofile caps A K
  filter_upwards [hquotes, ActualRunKineticGerm.rigidity run hG k q]
    with m hm hr
  intro datum hlevel Y F eta_w I M S hcal hFine
  subst m
  obtain ⟨hw, hstripe, hquote⟩ := hm datum rfl Y F eta_w I M S hcal
  have hgerm := ActualSelectedVacuumGerm.kinetic_germ run S hG hw hFine
  have hLaw := ActualSelectedVacuumGerm.lawful run S hG hw hstripe
  have hbeta := hr datum.cutoff datum.period datum.below.le (shell run S) hgerm
    (run.family.path.levels.params datum.level).width
    (run.family.path.levels.params datum.level).paths
    (run.family.path.levels.clock.loopCap datum.level)
    (regularPrice run I M) (run.family.path.levels.clock.forcedAllowance datum.level)
    hLaw hquote
  rw [ActualSelectedVacuumGerm.beta] at hbeta
  exact hbeta

end YM.Integration.ActualSelectedVacuumBeta
end
