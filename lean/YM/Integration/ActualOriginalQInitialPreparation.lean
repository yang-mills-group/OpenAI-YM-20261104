import YM.Integration.ActualOriginalQInitialInput
import YM.Integration.ActualRunRequestedWidth
import YM.Integration.ActualRunRequestedNorm
import YM.Integration.ActualRequestedStartupPhysical
import YM.Integration.ActualStartupNormalizedQ
import YM.Integration.FullQLocalFullPreparedInputAt
import YM.Integration.LocalComparisonBarePreparationAt

/-! Full physical preparation of the concrete original-Q initial input.
The carrier is the original top representative. The entire startup chip,
all original forced gas and the H-normalized full Q source are retained.
The only changed source datum is the proof of its already equal origins. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalQInitialPreparation
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato PhysicalNext.ThroughLaunch
open LocalComparison LocalComparison.Global RG3.Script.Picnic
open FullQLocal FullQLocal.RenderedStep
open IterationFour IterationFour.Vacuum
open scoped Classical BigOperators Topology

variable {G : Gauge} {B : MS.Local.Physical.Deck G}
    {V : Type} [DecidableEq V] [Fintype V]
    (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B)
    (J : Request V) (A : NumericSchedule R.family J)

local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "A₀" => ActualOriginalQInitialInput.schedule R hG u J A

variable (d : LocalFormal.Datum R.family (Stock.census V))
    (Q : MS.Land.Prescription B)
    (o : V → Site (R.family.side (d.level + 1) d.period))
    (μ : ℝ) (orders : V → ℕ)

local notation "D₀" =>
  ActualOriginalQPointSetup.pointDatum R J d.period (d.level + 1) o
local notation "clock₀" => μ - R.family.S.scale d.cutoff
local notation "c₀" => ActualOriginalQInitialInput.scales R hG u J A d Q o μ orders

/-- The complete original representation is used without changing any
path, activity, scalar, beta or vacuum value. -/
def carrier : PhysicalCarrier R.family d.cutoff d.period (d.level + 1) where
  rep := R.family.path.rep d.cutoff d.period (d.level + 1)
  path := rfl
  clip := rfl
  point := (R.makes.wilson.represents d.cutoff d.period (d.level + 1)
    (Nat.succ_le_of_lt d.below)).vac

private def withRoot {X : Type*} {n : Side} {P : Rep G n} {marks : Census V}
    {v w : V → Site n} (T : Taste X v P marks) (h : v = w) : Taste X w P marks where
  menu := T.menu
  root := T.root.trans h
  tag := T.tag
  site := T.site
  score := T.score

omit [Fintype V] in
private theorem withRoot_leaf {X : Type*} {n : Side} {P : Rep G n} {marks : Census V}
    {v w : V → Site n} (T : Taste X v P marks) (h : v = w) (x : X) :
    (withRoot T h).leaf x = T.leaf x := rfl

omit [Fintype V] in
private theorem pullback_leaf {X Y : Type*} {n : Side} {P : Rep G n} {marks : Census V}
    {v : V → Site n} (f : X → Y) (T : Taste Y v P marks) (x : X) :
    (pullback f T).leaf x = T.leaf (f x) := rfl

section Input
variable [Nonempty V]

/-- Only the proof of the original origins changes. The full pulled-back
menu, all gas rows, captions and coefficients are copied literally. -/
def input : Taste (TestSpace (J₀).tests) o (carrier R d).rep (Stock.census V) := by
  let T := pullback (VariableScaling.tests c₀)
    (ActualOriginalQInput.input Q D₀ u clock₀ orders hG d.cutoff
      (Nat.succ_le_of_lt d.below))
  have ho : (ActualOriginalQPackets.positions D₀ u).origin = o := by
    funext v
    exact ActualOriginalQPointDatum.root_eq R _ _ _ _ _ v
  exact withRoot T ho

private theorem input_leaf (x : TestSpace (J₀).tests) :
    (input R hG u J A d Q o μ orders).leaf x =
      (ActualOriginalQInput.input Q D₀ u clock₀ orders hG d.cutoff
        (Nat.succ_le_of_lt d.below)).leaf (VariableScaling.tests c₀ x) := by
  let raw := ActualOriginalQInput.input Q D₀ u clock₀ orders hG d.cutoff
    (Nat.succ_le_of_lt d.below)
  have ho : (ActualOriginalQPackets.positions D₀ u).origin = o := by
    funext v
    exact ActualOriginalQPointDatum.root_eq R _ _ _ _ _ v
  exact (withRoot_leaf (pullback (VariableScaling.tests c₀) raw) ho x).trans
    (pullback_leaf (VariableScaling.tests c₀) raw x)

/-- Equality of the full polynomial density, before any quotient, field
integral, mode selection or selected-model choice. -/
theorem input_density (x : TestSpace (J₀).tests)
    (U : Config G (R.family.side (d.level + 1) d.period)) :
    ((input R hG u J A d Q o μ orders).leaf x).density U =
      ((ActualOriginalQInput.input Q D₀ u clock₀ orders hG d.cutoff
        (Nat.succ_le_of_lt d.below)).leaf (VariableScaling.tests c₀ x)).density U := by
  exact congrArg (fun L => L.density U) (input_leaf R hG u J A d Q o μ orders x)

theorem input_multilinear :
    Multilinear (J₀).tests (input R hG u J A d Q o μ orders) := by
  have h := InputScaling.multilinear c₀ _
    (ActualOriginalQInput.multilinear Q D₀ u clock₀ orders hG d.cutoff
      (Nat.succ_le_of_lt d.below))
  exact {
    regular := h.regular
    forced := h.forced
    unit := h.unit
    captions := h.captions }

/-- Singleton insertion addresses are restrictions of the original full
stub receipt. Every actual row support and token footprint is unchanged. -/
theorem input_retains :
    FunctionalRetains (input R hG u J A d Q o μ orders) (fun v => {o v}) := by
  have h := ActualOriginalQInput.retains Q D₀ u clock₀ orders hG d.cutoff
    (Nat.succ_le_of_lt d.below)
  have hs : FunctionalRetains (input R hG u J A d Q o μ orders)
      (ActualOriginalQPackets.positions D₀ u).stub := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v
      have hv := (ActualOriginalQPackets.positions D₀ u).mem v
      change ActualRunQlocalNativeTuple.root D₀ v ∈
        (ActualOriginalQPackets.positions D₀ u).stub v at hv
      simpa only [ActualOriginalQPointSetup.pointDatum, ActualOriginalQPointDatum.root_eq] using hv
    · rintro i v ⟨x,U,hx⟩ hv
      exact h.regular i v ⟨VariableScaling.tests c₀ x,U,hx⟩ hv
    · rintro i j v ⟨x,U,hx⟩ hv
      exact h.forced i j v ⟨VariableScaling.tests c₀ x,U,hx⟩ hv
    · rintro i v ⟨x,hx⟩ hv
      exact h.captions i v ⟨VariableScaling.tests c₀ x,hx⟩ hv
  exact hs.singleton_addresses

private theorem active_zero :
    ((input R hG u J A d Q o μ orders).leaf (fun v => (0 : ((J₀).tests v).Mood))).Active :=
  InputScaling.active_zero c₀ _
    (ActualOriginalQInput.active_zero Q D₀ u clock₀ orders hG d.cutoff
      (Nat.succ_le_of_lt d.below))

end Input

variable (hStage : WithStage R.metals.p OriginalRunConstruction.originalOrders)

private def eligible (m : ℕ) : Prop :=
  ActualOriginalQInitialInput.start R hG u J A
    (OriginalRunConstruction.profile_orders R hStage) ≤ m ∧
  (J₀).inputSupport ≤ (R.family.path.levels.budget (m + 1)).supportExponent ∧
  ActualOriginalQLayout.referenceLevel R u ≤ m + 1 ∧
  ∀ period : ℕ,
    0 ≤ ActualStartupRequestedRemainder.cost R (J₀).order (J₀).eta (m + 1) ∧
    (ActualStartupMaskedAction.remainder R (m + 1) period (J₀).order).Invoice
      ((A₀).inputNorm m)
      (ActualStartupRequestedRemainder.cost R (J₀).order (J₀).eta (m + 1)) ∧
    ActualStartupRequestedRemainder.cost R (J₀).order (J₀).eta (m + 1) ≤
      (J₀).inheritedConstant *
        Pert.Asymptotics.regulatorRun R.family (m + 1) period (m + 1) ^
          (((J₀).order : ℝ) + 1 - (J₀).eta)

omit [DecidableEq V] in
private theorem eventually_eligible :
    ∀ᶠ m : ℕ in atTop, eligible R hG u J A hStage m := by
  obtain ⟨n, hn⟩ := eventually_atTop.1
    (ActualRunRequestedWidth.eventually_support R hStage (J₀).inputSupport)
  have hi := ActualOriginalQRequest.eventually_invoice R u J A hG
  filter_upwards [
    eventually_ge_atTop (ActualOriginalQInitialInput.start R hG u J A
      (OriginalRunConstruction.profile_orders R hStage)),
    eventually_ge_atTop n,
    eventually_ge_atTop (ActualOriginalQLayout.referenceLevel R u), hi]
    with m hm hs hr hI
  exact ⟨hm, hn (m + 1) (hs.trans (Nat.le_succ m)),
    hr.trans (Nat.le_succ m), hI⟩

/-- One tail precedes the original roots, period, fee clock and all tests. -/
def start : ℕ :=
  (eventually_atTop.1 (eventually_eligible R hG u J A hStage)).choose

private theorem eligible_of_start
    (hm : start R hG u J A hStage ≤ d.level) :
    eligible R hG u J A hStage d.level :=
  (eventually_atTop.1 (eventually_eligible R hG u J A hStage)).choose_spec d.level hm

/-- This is the previously constructed Numeric input on the common tail,
not a new choice of its colors, vacuum or physical source. -/
def analyticInput
    (hm : start R hG u J A hStage ≤ d.level)
    (hperiod : (J₀).physicalPeriodLower ≤ (R.family.S.period d.period).val) :
    Numeric.AnalyticInput J₀ A₀ d :=
  ActualOriginalQInitialInput.input R hG u J A d Q o μ orders
    (OriginalRunConstruction.profile_orders R hStage)
    (eligible_of_start R hG u J A d hStage hm).1 hperiod

private def wellFormed (F : Numeric.AnalyticInput J₀ A₀ d)
    (hSupport : (J₀).inputSupport ≤
      (R.family.path.levels.budget (d.level + 1)).supportExponent) :
    WellFormed ((A₀).inputNorm d.level) (carrier R d).rep := by
  have hv := (R.makes.wilson.represents d.cutoff d.period (d.level + 1)
    (Nat.succ_le_of_lt d.below)).vac
  apply ActualRunRequestedNorm.wellFormed R d.cutoff d.period (d.level + 1)
    (Nat.succ_le_of_lt d.below) ((A₀).inputNorm d.level)
  · exact ((A₀).input_norm d.level).threshold.trans
      (congrArg BudgetPoint.threshold hv).symm
  · exact ((A₀).input_norm d.level).block.trans
      (congrArg BudgetPoint.B hv).symm
  · exact (((A₀).input_norm d.level).order.le.trans F.input_field_admitted).trans_eq
      (congrArg BudgetPoint.order hv).symm
  · exact (((A₀).input_norm d.level).distance.le.trans F.input_distance_admitted).trans_eq
      (congrArg BudgetPoint.power hv).symm
  · exact (((A₀).input_norm d.level).reserve.le.trans hSupport).trans_eq
      (congrArg BudgetPoint.supportExponent hv).symm

private def calibrationAt (m per N : ℕ) (h : N = m + 1) :
    CalibrationPresentation (R.family.path.rep N per (m+1)) ((A₀).inputNorm m) 0 :=
  h.symm ▸ ActualRequestedStartupPhysical.calibration R J₀ A₀ m per

omit [DecidableEq V] in
private theorem calibrationAt_amount (m per N : ℕ) (h : N = m + 1)
    (U : Config G (R.family.side (m+1) per)) :
    (calibrationAt R hG u J A m per N h).amount U =
      (ActualRequestedStartupPhysical.calibration R J₀ A₀ m per).amount U := by
  subst N
  rfl

private def calibration (htop : d.cutoff = d.level + 1) :
    CalibrationPresentation (carrier R d).rep ((A₀).inputNorm d.level) 0 :=
  calibrationAt R hG u J A d.level d.period d.cutoff htop

private theorem references
    (hm : start R hG u J A hStage ≤ d.level) :
    ∀ s : ActualOriginalQReaders.Slot u, R.family.ref s.2.size ≤ d.level + 1 := by
  intro s
  exact ActualOriginalQLayout.reference_le R u
    (eligible_of_start R hG u J A d hStage hm).2.2.1 s

section Prepared
variable [Nonempty V]

/-- Every mode of the complete normalized input is Haar-integrable on the
actual initial torus. The full original gas stays in this numerator. -/
theorem input_integrable
    (hm : start R hG u J A hStage ≤ d.level)
    (htop : d.cutoff = d.level + 1)
    (x : TestSpace (J₀).tests) (s : (Stock.census V).Mode) :
    Integrable (fun U =>
      (((input R hG u J A d Q o μ orders).leaf x).density U).part s)
      (prior G (R.family.side (d.level + 1) d.period)) := by
  have he : (fun U =>
      (((input R hG u J A d Q o μ orders).leaf x).density U).part s) =
      (fun U => (((ActualOriginalQInput.input Q D₀ u clock₀ orders hG
        (d.level + 1) le_rfl).leaf (VariableScaling.tests c₀ x)).density U).part s) := by
    funext U
    have hcut (N : ℕ) (hN : d.level + 1 ≤ N) (heq : N = d.level + 1) :
        ((ActualOriginalQInput.input Q D₀ u clock₀ orders hG N hN).leaf
          (VariableScaling.tests c₀ x)).density U =
        ((ActualOriginalQInput.input Q D₀ u clock₀ orders hG (d.level+1) le_rfl).leaf
          (VariableScaling.tests c₀ x)).density U := by
      subst N
      rfl
    exact congrArg (fun z => z.part s) ((input_density R hG u J A d Q o μ orders x U).trans
      (hcut d.cutoff (Nat.succ_le_of_lt d.below) htop))
  rw [he]
  exact ActualStartupNormalizedQ.input_integrable Q D₀ u clock₀ orders hG
    (references R hG u J A d hStage hm) (VariableScaling.tests c₀ x) s

/-- Actual full preparation at the original initial step. The complete
chip is paid at the requested norm; the calibration price is literally zero. -/
def prepared
    (hm : start R hG u J A hStage ≤ d.level)
    (hperiod : (J₀).physicalPeriodLower ≤ (R.family.S.period d.period).val)
    (htop : d.cutoff = d.level + 1) (T : Campaign R) :
    Numeric.FullPreparedInputAt
      (analyticInput R hG u J A d Q o μ orders hStage hm hperiod) 0 := by
  let F := analyticInput R hG u J A d Q o μ orders hStage hm hperiod
  have he := eligible_of_start R hG u J A d hStage hm
  have hi := he.2.2.2 d.period
  refine {
    carrier := carrier R d
    wellFormed := wellFormed R hG u J A d F he.2.1
    inherited := ActualStartupRequestedRemainder.cost R (J₀).order (J₀).eta (d.level + 1)
    inherited_nonnegative := hi.1
    inherited_bound := ?_
    error := ActualStartupMaskedAction.remainder R (d.level + 1) d.period (J₀).order
    error_paid := hi.2.1
    calibration := calibration R hG u J A d htop
    exponent := ?_
    input := input R hG u J A d Q o μ orders
    multilinear := input_multilinear R hG u J A d Q o μ orders
    input_retains := input_retains R hG u J A d Q o μ orders
    regularPrice := 0
    forcedPrice := 0
    forced_bound := (J₀).forced_constant_nonnegative
    prepared := ?_ }
  · simpa only [htop] using hi.2.2
  · intro U
    rw [show (calibration R hG u J A d htop).amount U = _ from
      calibrationAt_amount R hG u J A d.level d.period d.cutoff htop U]
    simpa only [carrier, htop, F, analyticInput,
      ActualOriginalQInitialInput.input, ActualOriginalQInitialInput.album] using
      (ActualRequestedStartupPhysical.physical_exponent R J₀ A₀ T
        d.level d.period U)
  · apply PreparedWithRemainderAt.of_bare_factorization
      d.cutoff d.period (d.level + 1) ((A₀).inputNorm d.level)
      (Handoff.legacyCarrier (carrier R d)) F.fineRoots
      (input R hG u J A d Q o μ orders) F.colors F.packets F.inputRadii
      (envelopeProduct F.kernelCosts) (fun v => (0 : ((J₀).tests v).Mood))
    · exact active_zero R hG u J A d Q o μ orders
    · exact F.convention
    · exact F.input_radius_positive
    · intro s
      exact Finset.prod_pos (fun i _ => F.kernel_positive i)
    · rfl
    · exact ActualRunQlocalNativeTuple.packet_gas_summable R d.cutoff d.period
        (d.level + 1) (Nat.succ_le_of_lt d.below)
    · intro x U
      change ((input R hG u J A d Q o μ orders).leaf x).density U =
        ((R.family.path.rep d.cutoff d.period (d.level + 1)).eval U : ℂ) •
          Poly.pass ((VariableScaling.packets c₀
            (ActualOriginalQFrozenInput.packets Q D₀ u clock₀ orders d.cutoff)).read x
              (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period
                (d.level + 1)) U)
      refine (input_density R hG u J A d Q o μ orders x U).trans ?_
      rw [VariableScaling.read]
      exact ActualOriginalQFrozenInput.density_packet_factor Q D₀ u clock₀ orders
        hG d.cutoff (Nat.succ_le_of_lt d.below)
        (references R hG u J A d hStage hm)
        (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level + 1))
        (VariableScaling.tests c₀ x) U

/-- The actual full source and its zero auxiliary marked prices are exposed
for the retained grant and for the original finite-Q Deck identification. -/
theorem prepared_fields
    (hm : start R hG u J A hStage ≤ d.level)
    (hperiod : (J₀).physicalPeriodLower ≤ (R.family.S.period d.period).val)
    (htop : d.cutoff = d.level + 1) (T : Campaign R) :
    let I := prepared R hG u J A d Q o μ orders hStage hm hperiod htop T
    I.carrier.rep = R.family.path.rep d.cutoff d.period (d.level + 1) ∧
      I.input = input R hG u J A d Q o μ orders ∧
      I.regularPrice = 0 ∧ I.forcedPrice = 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Prepared

end YM.Integration.ActualOriginalQInitialPreparation
end
