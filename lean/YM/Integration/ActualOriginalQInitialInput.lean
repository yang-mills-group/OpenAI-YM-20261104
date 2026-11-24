import YM.Integration.ActualOriginalQPointSetup
import YM.Integration.ActualBoundedNumericSchedule
import YM.Integration.ActualOriginalQPointCover
import YM.Integration.ActualOriginalQNormalization
import YM.Integration.FullQLocalInputScaling
import YM.Integration.LocalComparisonAddressRestriction
import YM.Integration.FullQLocalNumericStepData
import YM.Integration.ActualRunFixedOrders

/-! The concrete normalized original-Q analytic input, chosen before F or M.
The full finite Q bill determines its test normalization. The original
startup album, native path, every Glyph, and all token footprints remain.
The profile receipt belongs to the same original Run construction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalQInitialInput
open Function Filter Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison
open FullQLocal FullQLocal.RenderedStep
open IterationFour IterationFour.Vacuum
open scoped Classical BigOperators Topology

variable {G : Gauge} {B : MS.Local.Physical.Deck G}
    {V : Type} [DecidableEq V] [Fintype V]
    (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B)
    (J : Request V) (A : NumericSchedule R.family J)

local notation "J₀" => ActualOriginalQPointSetup.request R u J

/-- Width is genuinely clipped before selecting the input; all changed
numerical schedule duties are proved by the bounded-schedule constructor. -/
def schedule : NumericSchedule R.family J₀ :=
  ActualBoundedNumericSchedule.bounded R hG
    (ActualOriginalQPointSetup.schedule R u J A)

local notation "A₀" => schedule R hG u J A

def album (m period : ℕ) :=
  ActualStartupInvoice.paidAlbum G (R.family.side (m + 1) period)
    ((A₀).inputNorm m) (R.family.path.levels.params (m + 1))
    (J₀).order ((A₀).inputWidth m)

variable (d : LocalFormal.Datum R.family (Stock.census V))
    (Q : MS.Land.Prescription B)
    (o : V → Site (R.family.side (d.level + 1) d.period))
    (μ : ℝ) (orders : V → ℕ)

local notation "D₀" =>
  ActualOriginalQPointSetup.pointDatum R J d.period (d.level + 1) o
local notation "clock₀" => μ - R.family.S.scale d.cutoff

/-- Every original fee, reader, tensor and path factor is retained. -/
def normalizer : ℝ :=
  ActualOriginalQNormalization.normalizer Q D₀ u μ orders d.cutoff
    (fun _ => 1) ((A₀).inputWidth d.level)

def scales : V → ℂ := fun _ =>
  (normalizer R hG u J A d Q o μ orders : ℂ)⁻¹

local notation "c₀" => scales R hG u J A d Q o μ orders

def packets :=
  FullQLocal.VariableScaling.packets c₀
    (ActualOriginalQPointSetup.packets R u J d Q o clock₀ orders)

def colors :=
  fun x => ActualOriginalQStartupAction.colors (J := J₀) (datum := d)
    Q D₀ u clock₀ orders A₀ rfl
      (FullQLocal.VariableScaling.tests c₀ x)

def cover : ℕ :=
  ActualOriginalQPackets.packetCover Q D₀ u clock₀ orders d.cutoff
    ((A₀).inputNorm d.level)

private theorem normalizer_ge_one :
    1 ≤ normalizer R hG u J A d Q o μ orders := le_max_left _ _

private theorem finite_cost_le :
    ActualOriginalQPackets.packetCost Q D₀ u clock₀ orders d.cutoff
      (fun _ => 1) ((A₀).inputWidth d.level) ≤
        normalizer R hG u J A d Q o μ orders := by
  rw [ActualOriginalQCharges.packet_cost D₀ u Q clock₀ orders d.cutoff
    (Nat.succ_le_of_lt d.below) (fun _ => 1) ((A₀).inputWidth d.level)]
  exact le_max_right _ _

/-- Normalization pays the complete original packet at the actual requested
norm. Singleton insertion addresses do not shrink any token footprint. -/
theorem paid :
    (packets R hG u J A d Q o μ orders).Paid
      ((A₀).inputNorm d.level) (fun v => {o v})
      (ActualRunQlocalNativeTuple.readerRegion D₀) (fun _ => 1)
      (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level + 1))
      ((A₀).inputWidth d.level) ((A₀).admittedCost d.level)
      (cover R hG u J A d Q o μ orders) 0 := by
  have hraw := ActualOriginalQFrozenInput.packets_paid Q D₀ u clock₀ orders
    d.cutoff
    (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level + 1))
    ((A₀).inputNorm d.level) (fun _ => 1) ((A₀).inputWidth d.level)
    ((A₀).input_width_pos d.level) (fun _ => zero_lt_one)
  have hn := FullQLocal.FixedRadiusScaling.paid_normalized
    (ActualOriginalQFrozenInput.packets Q D₀ u clock₀ orders d.cutoff) hraw
    (normalizer R hG u J A d Q o μ orders)
    (normalizer_ge_one R hG u J A d Q o μ orders)
    (finite_cost_le R hG u J A d Q o μ orders)
  have ho : ∀ v, o v ∈ (ActualOriginalQPackets.positions D₀ u).stub v := by
    intro v
    have hv := (ActualOriginalQPackets.positions D₀ u).mem v
    change ActualRunQlocalNativeTuple.root D₀ v ∈
      (ActualOriginalQPackets.positions D₀ u).stub v at hv
    simpa only [ActualOriginalQPointSetup.pointDatum, ActualOriginalQPointDatum.root_eq] using hv
  have hs := hn.singleton_addresses o ho
  refine { hs with roots := ?_ }
  intro v
  exact Push.Local.sumBudget_mono (hs.roots v) (hs.roots v).1
    (fun _ => le_rfl) ((A₀).admitted_cost_ge_one d.level)

private theorem cover_bound :
    cover R hG u J A d Q o μ orders ≤ ActualOriginalQPointCover.bound R u :=
  ActualOriginalQPointCover.packet_cover R u d.period (d.level + 1) o
    (fun i => (J.tests i).D) (fun _ => 0) Q clock₀ orders
    d.cutoff ((A₀).inputNorm d.level)

private theorem convention
    (H : GradedVacuumLayers (album R hG u J A d.level d.period)
      ((A₀).inputNorm d.level) (J₀).order (J₀).vacuumRankCap
      ((A₀).inputWidth d.level) ((A₀).admittedCost d.level)) :
    InputColors (colors R hG u J A d Q o μ orders)
      (packets R hG u J A d Q o μ orders) :=
  FullQLocal.InputScaling.input_colors c₀
    (ActualOriginalQStartupAction.colors (J := J₀) (datum := d)
      Q D₀ u clock₀ orders A₀ rfl)
    (ActualOriginalQPointSetup.packets R u J d Q o clock₀ orders)
    (ActualOriginalQStartupAction.input_colors (J := J₀) (datum := d) (A := A₀)
      Q D₀ u clock₀ orders H rfl)

private theorem whole
    (H : GradedVacuumLayers (album R hG u J A d.level d.period)
      ((A₀).inputNorm d.level) (J₀).order (J₀).vacuumRankCap
      ((A₀).inputWidth d.level) ((A₀).admittedCost d.level)) :
    Nonempty (FineWholeAction J₀ d (colors R hG u J A d Q o μ orders)
      (album R hG u J A d.level d.period)) :=
  ActualLayerFineAction.whole_action R (Stock.census V) J₀ d
    (layers := album R hG u J A d.level d.period) (p := (A₀).inputNorm d.level)
    (order := (J₀).order) (rankCap := (J₀).vacuumRankCap)
    (width := (A₀).inputWidth d.level) (budget := (A₀).admittedCost d.level) H
    ((A₀).input_width_pos d.level) (colors R hG u J A d Q o μ orders)
    (packets R hG u J A d Q o μ orders)
    (convention R hG u J A d Q o μ orders H) (fun _ => rfl)

private def eligible (m : ℕ) : Prop :=
  (∀ period, Nonempty (GradedVacuumLayers (album R hG u J A m period)
    ((A₀).inputNorm m) (J₀).order (J₀).vacuumRankCap
    ((A₀).inputWidth m) ((A₀).admittedCost m))) ∧
  (J₀).inputFieldOrder ≤ (R.family.path.levels.budget (m + 1)).order ∧
  (J₀).inputDistanceOrder ≤ (R.family.path.levels.budget (m + 1)).power ∧
  (J₀).outputFieldOrder ≤ (R.family.path.levels.budget m).order ∧
  (J₀).outputDistanceOrder ≤ (R.family.path.levels.budget m).power ∧
  (∀ v, R.family.ref ((J₀).outputWeight v) ≤ m) ∧
  Real.exp ((J₀).inputSupport * (ActualOriginalQPointCover.bound R u : ℝ)) ≤
    (A₀).admittedCost m

variable
    (hprofile : ∀ j, j ≤ (R.metals.p.profile j).order ∧
      j ≤ (R.metals.p.profile j).power)

omit [DecidableEq V] in
include hprofile in
private theorem eventually_eligible :
    ∀ᶠ m : ℕ in atTop, eligible R hG u J A m := by
  let order := max (max (J₀).inputFieldOrder (J₀).inputDistanceOrder)
    (max (J₀).outputFieldOrder (J₀).outputDistanceOrder)
  let refs := (Finset.univ : Finset V).sup fun v => R.family.ref ((J₀).outputWeight v)
  have ho := R.family.path.levels.fits.deep.eventually_ge_atTop order
  have hl := ActualStartupAdmittedAlbum.eventually_paid_layers R hG J₀ A₀
    (ActualOriginalQPointSetup.limits R u J).1
  have hc := ActualStartupAdmittedAlbum.eventually_cost R hG J₀ A₀
    (Real.exp ((J₀).inputSupport * (ActualOriginalQPointCover.bound R u : ℝ)))
  filter_upwards [hl, ho, eventually_ge_atTop refs, hc] with m hL hO hR hC
  obtain ⟨hi, hp⟩ := ActualRunFixedOrders.budget_orders R hprofile (m + 1)
  obtain ⟨hi', hp'⟩ := ActualRunFixedOrders.budget_orders R hprofile m
  have hnext := R.family.path.levels.fits.mono (Nat.le_succ m)
  have h1 : (J₀).inputFieldOrder ≤ order :=
    (le_max_left _ _).trans (le_max_left _ _)
  have h2 : (J₀).inputDistanceOrder ≤ order :=
    (le_max_right _ _).trans (le_max_left _ _)
  have h3 : (J₀).outputFieldOrder ≤ order :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h4 : (J₀).outputDistanceOrder ≤ order :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨fun period => hL period
    (ActualBoundedNumericSchedule.input_width_le_one R hG
      (ActualOriginalQPointSetup.schedule R u J A) m),
    (h1.trans hO).trans (hnext.trans hi),
    (h2.trans hO).trans (hnext.trans hp),
    (h3.trans hO).trans hi', (h4.trans hO).trans hp', ?_, hC⟩
  intro v
  exact (Finset.le_sup (f := fun i => R.family.ref ((J₀).outputWeight i))
    (Finset.mem_univ v)).trans hR

/-- One stage is chosen before every cutoff, period, root and fee order. -/
def start : ℕ :=
  (eventually_atTop.1 (eventually_eligible R hG u J A hprofile)).choose

private theorem eligible_of_start
    (hm : start R hG u J A hprofile ≤ d.level) :
    eligible R hG u J A d.level :=
  (eventually_atTop.1 (eventually_eligible R hG u J A hprofile)).choose_spec
    d.level hm

include Q o μ orders in
/-- This is an actual Numeric input. Every analytic, payment, cover and
finite-order field is constructed from the same preselected data. -/
def input
    (hm : start R hG u J A hprofile ≤ d.level)
    (hperiod : (J₀).physicalPeriodLower ≤ (R.family.S.period d.period).val) :
    Numeric.AnalyticInput J₀ A₀ d := by
  have he := eligible_of_start R hG u J A d hprofile hm
  let H := Classical.choice (he.1 d.period)
  refine
    { whole_tests := ActualOriginalQPointSetup.whole_tests R u J
      layers := album R hG u J A d.level d.period
      layers_paid := ActualStartupInvoice.paid_permits G _ _ _ _ _
        ((A₀).input_width_pos d.level)
      vacuum := H
      fineRoots := o
      coarseRoots := fun v =>
        (R.family.path.levels.clock.op d.level d.period).ratio.parent (o v)
      roots := fun _ => rfl
      colors := colors R hG u J A d Q o μ orders
      packets := packets R hG u J A d Q o μ orders
      convention := convention R hG u J A d Q o μ orders H
      rank_bounded := ?_
      power_bounded := ?_
      whole_input := Classical.choice (whole R hG u J A d Q o μ orders H)
      inputRadii := fun _ => 1
      outputRadii := fun _ => ((A₀).radiusLoss d.level)⁻¹
      kernelCosts := fun _ => 1
      input_radius_positive := fun _ => zero_lt_one
      output_radius_positive := fun _ => inv_pos.mpr ((A₀).radius_loss_positive d.level)
      kernel_positive := fun _ => zero_lt_one
      radius_admission := fun _ => ?_
      inputAddresses := fun v => {o v}
      input_origins := fun v => Finset.mem_singleton_self (o v)
      inputRegion := ActualRunQlocalNativeTuple.readerRegion D₀
      coverOffset := cover R hG u J A d Q o μ orders
      coverSlope := 0
      cover_cost := ?_
      input_paid := ?_
      physical_period := hperiod
      input_field_admitted := he.2.1
      input_distance_admitted := he.2.2.1
      output_field_admitted := he.2.2.2.1
      output_distance_admitted := he.2.2.2.2.1
      primary_admitted := he.2.2.2.2.2.1 }
  · change ActualOriginalQLayout.rankCap R u ≤ (J₀).inputPacketRankCap
    exact (ActualOriginalQPointSetup.limits R u J).2.1
  · change 0 ≤ (J₀).inputPacketPowerCap
    exact Nat.zero_le _
  · exact (inv_mul_cancel₀ ((A₀).radius_loss_positive d.level).ne').le
  · rw [((A₀).input_norm d.level).reserve]
    exact (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (cover_bound R hG u J A d Q o μ orders))
        (J₀).input_support_pos.le)).trans he.2.2.2.2.2.2
  · simpa only [div_one] using paid R hG u J A d Q o μ orders

/-- These identities expose the original roots, exact normalization and
full startup album for the physical preparation and selected-output join. -/
theorem input_fields
    (hm : start R hG u J A hprofile ≤ d.level)
    (hperiod : (J₀).physicalPeriodLower ≤ (R.family.S.period d.period).val) :
    let F := input R hG u J A d Q o μ orders hprofile hm hperiod
    F.fineRoots = o ∧ F.inputAddresses = (fun v => {o v}) ∧
      F.inputRadii = (fun _ => 1) ∧ F.kernelCosts = (fun _ => 1) ∧
      F.packets = packets R hG u J A d Q o μ orders ∧
      F.colors = colors R hG u J A d Q o μ orders ∧
      F.layers = album R hG u J A d.level d.period := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end YM.Integration.ActualOriginalQInitialInput
end
