import YM.Integration.ActualOriginalQInitialPreparation
import YM.Integration.FullQLocalRetainedOutput

/-! Initial full preparation from a bound on the actual startup carrier.
The original normalized input, complete startup remainder, and both native
and requested forced bounds are retained. The analytic input uses the
same fixed Run's order/power receipt; no growing support profile is used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalQInitialAtTop
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global
open RG3.Script.Picnic FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric.Retained
open IterationFour IterationFour.Vacuum
open scoped Classical BigOperators Topology

variable {G : Gauge} {B : MS.Local.Physical.Deck G}
    {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B)
    (J : Request V) (A : NumericSchedule R.family J)
    (d : LocalFormal.Datum R.family (Stock.census V))
    (Q : MS.Land.Prescription B)
    (o : V → Site (R.family.side (d.level + 1) d.period))
    (mu : ℝ) (orders : V → ℕ)

local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "A₀" => ActualOriginalQInitialInput.schedule R hG u J A
local notation "C₀" => ActualOriginalQInitialPreparation.carrier R d
local notation "D₀" =>
  ActualOriginalQPointSetup.pointDatum R J d.period (d.level + 1) o
local notation "clock₀" => mu - R.family.S.scale d.cutoff
local notation "c₀" => ActualOriginalQInitialInput.scales R hG u J A d Q o mu orders
local notation "T₀" => ActualOriginalQInitialPreparation.input R hG u J A d Q o mu orders

variable (T : Campaign R)
    (horders : ∀ k, k ≤ (R.metals.p.profile k).order ∧
      k ≤ (R.metals.p.profile k).power)
    (hfirst : ActualOriginalQInitialInput.start R hG u J A horders ≤ d.level)
    (hperiod : (ActualOriginalQPointSetup.request R u J).physicalPeriodLower ≤ (R.family.S.period d.period).val)
    (htop : d.cutoff = d.level + 1)
    (href : ∀ s : ActualOriginalQReaders.Slot u,
      R.family.ref s.2.size ≤ d.level + 1)
    (hchip :
      0 ≤ ActualStartupRequestedRemainder.cost R (ActualOriginalQPointSetup.request R u J).order (ActualOriginalQPointSetup.request R u J).eta (d.level + 1) ∧
      (ActualStartupMaskedAction.remainder R (d.level + 1) d.period (ActualOriginalQPointSetup.request R u J).order).Invoice
        ((ActualOriginalQInitialInput.schedule R hG u J A).inputNorm d.level)
        (ActualStartupRequestedRemainder.cost R (ActualOriginalQPointSetup.request R u J).order (ActualOriginalQPointSetup.request R u J).eta (d.level + 1)) ∧
      ActualStartupRequestedRemainder.cost R (ActualOriginalQPointSetup.request R u J).order (ActualOriginalQPointSetup.request R u J).eta (d.level + 1) ≤
        (ActualOriginalQPointSetup.request R u J).inheritedConstant *
          Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level + 1) ^
            (((ActualOriginalQPointSetup.request R u J).order : ℝ) + 1 - (ActualOriginalQPointSetup.request R u J).eta))
    (hvalid : (ActualOriginalQInitialPreparation.carrier R d).rep.activities.Valid ((ActualOriginalQInitialInput.schedule R hG u J A).inputNorm d.level)
      (R.family.path.levels.clock.allowance (d.level + 1))
      (R.family.path.levels.clock.forcedAllowance (d.level + 1)))

local notation "F₀" => ActualOriginalQInitialInput.input
  R hG u J A d Q o mu orders horders hfirst hperiod

/-- Every field is the original full startup datum. Only its well-formedness
proof uses the supplied actual requested-norm bound. -/
def prepared : Numeric.FullPreparedInputAt F₀ 0 := by
  let native := R.makes.wilson.represents d.cutoff d.period (d.level + 1)
    (Nat.succ_le_of_lt d.below)
  have hw : WellFormed ((A₀).inputNorm d.level) (C₀).rep := {
    threshold := ((A₀).input_norm d.level).threshold.trans
      (congrArg BudgetPoint.threshold native.vac).symm
    regular := fun i => hvalid.regular.smooth i
    regular_sum := fun U => (Activities.ESeries native.good.labels).summable U
    regularCost := R.family.path.levels.clock.allowance (d.level + 1)
    regular_cost_nonnegative := by
      obtain ⟨_, _, hs⟩ := hvalid.boundE
      have hz := hs (0 : Site (R.family.side (d.level + 1) d.period))
      exact (tsum_nonneg hz.1).trans hz.2.2
    regular_bound := hvalid.boundE
    forced := native.good.labels.forced
    moves := native.good.labels.moves }
  let atCut (N : ℕ) (h : N = d.level+1) : CalibrationPresentation
      (R.family.path.rep N d.period (d.level+1)) ((A₀).inputNorm d.level) 0 :=
    h.symm ▸ ActualRequestedStartupPhysical.calibration R J₀ A₀ d.level d.period
  have atCut_amount (N : ℕ) (h : N = d.level+1)
      (U : Config G (R.family.side (d.level+1) d.period)) :
      (atCut N h).amount U =
        (ActualRequestedStartupPhysical.calibration R J₀ A₀ d.level d.period).amount U := by
    subst N
    rfl
  let calibration : CalibrationPresentation (C₀).rep ((A₀).inputNorm d.level) 0 :=
    atCut d.cutoff htop
  refine {
    carrier := C₀
    wellFormed := hw
    inherited := ActualStartupRequestedRemainder.cost R (J₀).order (J₀).eta (d.level + 1)
    inherited_nonnegative := hchip.1
    inherited_bound := hchip.2.2
    error := ActualStartupMaskedAction.remainder R (d.level + 1) d.period (J₀).order
    error_paid := hchip.2.1
    calibration := calibration
    exponent := ?_
    input := T₀
    multilinear := ActualOriginalQInitialPreparation.input_multilinear
      R hG u J A d Q o mu orders
    input_retains := ActualOriginalQInitialPreparation.input_retains
      R hG u J A d Q o mu orders
    regularPrice := 0
    forcedPrice := 0
    forced_bound := (J₀).forced_constant_nonnegative
    prepared := ?_ }
  · intro U
    rw [show calibration.amount U = _ from atCut_amount d.cutoff htop U]
    simpa only [ActualOriginalQInitialPreparation.carrier, htop,
      ActualOriginalQInitialInput.input, ActualOriginalQInitialInput.album] using
      (ActualRequestedStartupPhysical.physical_exponent R J₀ A₀ T
        d.level d.period U)
  · apply PreparedWithRemainderAt.of_bare_factorization
      d.cutoff d.period (d.level + 1) ((A₀).inputNorm d.level)
      (Handoff.legacyCarrier C₀) (F₀).fineRoots T₀
      (F₀).colors (F₀).packets (F₀).inputRadii
      (envelopeProduct (F₀).kernelCosts) (fun v => (0 : ((J₀).tests v).Mood))
    · exact InputScaling.active_zero c₀ _
        (ActualOriginalQInput.active_zero Q D₀ u clock₀ orders hG d.cutoff
          (Nat.succ_le_of_lt d.below))
    · exact (F₀).convention
    · exact (F₀).input_radius_positive
    · intro s
      exact Finset.prod_pos (fun i _ => (F₀).kernel_positive i)
    · rfl
    · exact ActualRunQlocalNativeTuple.packet_gas_summable R d.cutoff d.period
        (d.level + 1) (Nat.succ_le_of_lt d.below)
    · intro x U
      change ((T₀).leaf x).density U =
        ((R.family.path.rep d.cutoff d.period (d.level + 1)).eval U : ℂ) •
          Poly.pass ((VariableScaling.packets c₀
            (ActualOriginalQFrozenInput.packets Q D₀ u clock₀ orders d.cutoff)).read x
              (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period
                (d.level + 1)) U)
      refine (ActualOriginalQInitialPreparation.input_density
        R hG u J A d Q o mu orders x U).trans ?_
      rw [VariableScaling.read]
      exact ActualOriginalQFrozenInput.density_packet_factor Q D₀ u clock₀ orders
        hG d.cutoff (Nat.succ_le_of_lt d.below) href
        (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level + 1))
        (VariableScaling.tests c₀ x) U

/-- Literal source and price identities for the iteration's initial state. -/
theorem prepared_fields :
    let I := prepared R hG u J A d Q o mu orders T horders hfirst hperiod
      htop href hchip hvalid
    I.carrier.rep = R.family.path.rep d.cutoff d.period (d.level + 1) ∧
      I.input = T₀ ∧ I.regularPrice = 0 ∧ I.forcedPrice = 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The two forced bounds refer to the same unchanged physical carrier. -/
theorem intake :
    NativeIntake (prepared R hG u J A d Q o mu orders T horders hfirst hperiod
      htop href hchip hvalid) := by
  have hnative : (C₀).rep.activities.KBound
      (R.family.path.levels.budget (d.level + 1))
      (R.family.path.levels.clock.forcedAllowance (d.level + 1)) := by
    have h := R.makes.wilson.represents d.cutoff d.period (d.level + 1)
      (Nat.succ_le_of_lt d.below)
    change (R.family.path.rep d.cutoff d.period (d.level + 1)).activities.KBound _ _
    have hv : (R.family.path.rep d.cutoff d.period (d.level+1)).p =
        R.family.path.levels.budget (d.level+1) := h.vac
    rw [← hv]
    exact h.good.labels.boundK
  exact ⟨hnative, hvalid.boundK, le_rfl, zero_le_one⟩

end YM.Integration.ActualOriginalQInitialAtTop
end
