import YM.Integration.ActualOriginalQInitialAtTop
import YM.Integration.ActualRunStartupCarrier
import YM.Integration.ActualStartupRequestedBudget
import YM.Integration.ActualRepeatedNorm

/-! The same actual ultraviolet carrier is valid at every fixed requested
norm. Its native startup estimates supply the missing initial preparation
receipt without any change to the common Run or its support profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Function Filter Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato RG.Shoot
open FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric.Retained
open scoped Classical Topology

namespace ActualRunStartupCarrier

/-- Every fixed requested norm is paid on the original full top carrier. -/
theorem eventually_valid {G : Gauge} (R : Run G) (hG : G.Simple)
    (T : Campaign R) (ord pow : ℕ) (supp : ℝ)
    (hord : 6 ≤ ord) (hpow : 2 ≤ pow) (hsupp : 0 < supp) :
    ∀ᶠ N : ℕ in atTop, ∀ period : ℕ,
      (R.family.path.rep N period N).activities.Valid
        (ActualRunAdmissionScales.requestedBudget R.family.path.levels
          N ord pow supp hord hpow hsupp)
        (R.family.path.levels.clock.allowance N)
        (R.family.path.levels.clock.forcedAllowance N) := by
  filter_upwards [ActualStartupRequestedBudget.eventually_valid
    R hG ord pow supp hord hpow hsupp] with N hN
  intro period
  let q := ActualRunAdmissionScales.requestedBudget R.family.path.levels
    N ord pow supp hord hpow hsupp
  have hband : (R.family.path.rep N period N).beta ∈
      band R.family.path.levels N :=
    ((T.goes N period).prices N (Nat.zero_le N) le_rfl).2
  have h := hN period (R.family.path.rep N period N).beta hband
    (R.alloy.B.kin.path N N) 0
  change (R.family.path.rep N period N).activities.Valid q _ _
  rw [top_activities_eq R T N period q rfl rfl]
  exact h

end ActualRunStartupCarrier

namespace ActualOriginalQInitialAtTop

variable {G : Gauge} {B : MS.Local.Physical.Deck G}
    {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]

/-- One tail precedes all original roots, periods, fee orders and tests.
The full startup chip is retained, and both forced bounds are supplied. -/
theorem eventually_prepared (R : Run G) (hG : G.Simple)
    (u : V → MS.Rake.Label B) (J : Request V)
    (A : NumericSchedule R.family J) (T : Campaign R)
    (horders : ∀ k, k ≤ (R.metals.p.profile k).order ∧
      k ≤ (R.metals.p.profile k).power) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (d : LocalFormal.Datum R.family (Stock.census V)),
      d.level = m →
      ∀ (Q : MS.Land.Prescription B)
        (o : V → Site (R.family.side (d.level + 1) d.period))
        (mu : ℝ) (orders : V → ℕ)
        (hperiod : (ActualOriginalQPointSetup.request R u J).physicalPeriodLower ≤
          (R.family.S.period d.period).val)
        (_htop : d.cutoff = d.level + 1),
      ∃ hfirst : ActualOriginalQInitialInput.start R hG u J A horders ≤ d.level,
      ∃ I : Numeric.FullPreparedInputAt
        (ActualOriginalQInitialInput.input R hG u J A d Q o mu orders
          horders hfirst hperiod) 0,
        NativeIntake I ∧
        I.carrier.rep = R.family.path.rep d.cutoff d.period (d.level + 1) ∧
        HEq I.input (ActualOriginalQInitialPreparation.input
          R hG u J A d Q o mu orders) ∧
        I.regularPrice = 0 ∧ I.forcedPrice = 0 := by
  let J₀ := ActualOriginalQPointSetup.request R u J
  let A₀ := ActualOriginalQInitialInput.schedule R hG u J A
  obtain ⟨first, hfirst⟩ := eventually_atTop.1
    (ActualRunStartupCarrier.eventually_valid R hG T
      J₀.inputFieldOrder J₀.inputDistanceOrder J₀.inputSupport
      (J₀.field_minimum.trans J₀.field_reserve)
      (J₀.distance_minimum.trans J₀.distance_reserve) J₀.input_support_pos)
  filter_upwards [
    eventually_ge_atTop (ActualOriginalQInitialInput.start R hG u J A horders),
    eventually_ge_atTop first,
    eventually_ge_atTop (ActualOriginalQLayout.referenceLevel R u),
    ActualOriginalQRequest.eventually_invoice R u J A hG]
    with m hm hlate href hchip
  intro d hd Q o mu orders hperiod htop
  subst m
  have references : ∀ s : ActualOriginalQReaders.Slot u,
      R.family.ref s.2.size ≤ d.level + 1 := fun s =>
    ActualOriginalQLayout.reference_le R u (href.trans (Nat.le_succ d.level)) s
  have hnorm : A₀.inputNorm d.level =
      ActualRunAdmissionScales.requestedBudget R.family.path.levels
        (d.level + 1) J₀.inputFieldOrder J₀.inputDistanceOrder J₀.inputSupport
        (J₀.field_minimum.trans J₀.field_reserve)
        (J₀.distance_minimum.trans J₀.distance_reserve) J₀.input_support_pos :=
    ActualRepeatedNorm.norm_unique R.family J₀.inputFieldOrder
      J₀.inputDistanceOrder J₀.inputSupport
      (J₀.field_minimum.trans J₀.field_reserve)
      (J₀.distance_minimum.trans J₀.distance_reserve) J₀.input_support_pos
      (d.level + 1) (A₀.inputNorm d.level) (A₀.input_norm d.level)
  have hv : (ActualOriginalQInitialPreparation.carrier R d).rep.activities.Valid
      (A₀.inputNorm d.level)
      (R.family.path.levels.clock.allowance (d.level + 1))
      (R.family.path.levels.clock.forcedAllowance (d.level + 1)) := by
    change (R.family.path.rep d.cutoff d.period (d.level + 1)).activities.Valid _ _ _
    rw [htop, hnorm]
    exact hfirst (d.level + 1) (hlate.trans (Nat.le_succ d.level)) d.period
  have hc :
      0 ≤ ActualStartupRequestedRemainder.cost R J₀.order J₀.eta (d.level + 1) ∧
      (ActualStartupMaskedAction.remainder R (d.level + 1) d.period J₀.order).Invoice
        (A₀.inputNorm d.level)
        (ActualStartupRequestedRemainder.cost R J₀.order J₀.eta (d.level + 1)) ∧
      ActualStartupRequestedRemainder.cost R J₀.order J₀.eta (d.level + 1) ≤
        J₀.inheritedConstant *
          Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level + 1) ^
            ((J₀.order : ℝ) + 1 - J₀.eta) := by
    obtain ⟨hq, hp, hb⟩ := hchip d.period
    refine ⟨hq, hp, ?_⟩
    rw [htop]
    exact hb
  let I := prepared R hG u J A d Q o mu orders T horders hm hperiod
    htop references hc hv
  exact ⟨hm, I,
    intake R hG u J A d Q o mu orders T horders hm hperiod htop references hc hv,
    rfl, HEq.rfl, rfl, rfl⟩

end ActualOriginalQInitialAtTop
end YM.Integration
end
