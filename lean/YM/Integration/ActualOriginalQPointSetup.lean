import YM.Integration.ActualOriginalQRequest
import YM.Integration.ActualOriginalQPointDatum
import YM.Integration.ActualOriginalQStartupAction

/-! Concrete whole-space point tests for the initial original-Q input.
The request is chosen before F or M. Its numerical norm/width/price data
are the original schedule data; no selected input is changed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalQPointSetup
open Filter Lattice Wilson RG Marker LocalComparison
open PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep
open scoped Classical Topology

variable {G : Gauge} (R : Run G) {B : MS.Local.Physical.Deck G}
    {V : Type} [DecidableEq V] [Fintype V]
    (u : V → MS.Rake.Label B) (J : Request V)

def request : Request V :=
  { ActualOriginalQRequest.request R u J with
    tests := fun i => QlocalNativeTests.orbit (J.tests i).D 0
    test_order := J.test_order }

def schedule (A : NumericSchedule R.family J) :
    NumericSchedule R.family (request R u J) where
  inputNorm := A.inputNorm
  outputNorm := A.outputNorm
  input_norm := A.input_norm
  output_norm := A.output_norm
  inputWidth := A.inputWidth
  outputWidth := A.outputWidth
  input_width_pos := A.input_width_pos
  output_width_pos := A.output_width_pos
  admittedCost := A.admittedCost
  admitted_cost_nonnegative := A.admitted_cost_nonnegative
  admitted_cost_ge_one := A.admitted_cost_ge_one
  radiusLoss := A.radiusLoss
  radius_loss_positive := A.radius_loss_positive
  radius_loss_ge_one := A.radius_loss_ge_one
  calibrationCap := A.calibrationCap
  calibration_cap_nonnegative := A.calibration_cap_nonnegative
  calibration_cap_tendsto := A.calibration_cap_tendsto
  cost_covers_widths := A.cost_covers_widths
  cost_covers_geometry := A.cost_covers_geometry
  cost_covers_units := A.cost_covers_units
  cost_subpower := A.cost_subpower
  pathRate := A.pathRate
  path_rate_positive := A.path_rate_positive
  path_rate_width := A.path_rate_width
  path_rate_cost := A.path_rate_cost
  regular_flat := A.regular_flat
  forced_flat := A.forced_flat

def pointDatum (p L : ℕ) (o : V → Site (R.family.side L p)) :=
  ActualOriginalQPointDatum.datum R p L o (fun i => (J.tests i).D) (fun _ => 0)

omit [DecidableEq V] in
theorem tests_eq (p L : ℕ) (o : V → Site (R.family.side L p)) :
    (request R u J).tests =
      ActualRunQlocalNativeTuple.orbit (pointDatum R J p L o) := rfl

omit [DecidableEq V] in
theorem whole_tests (i : V) :
    ∃ k w : ℕ, (request R u J).tests i = ⟨.whole, k, w⟩ :=
  ⟨(J.tests i).D, 0, rfl⟩

omit [DecidableEq V] in
theorem limits :
    (request R u J).order + 2 ≤ (request R u J).vacuumRankCap ∧
    ActualOriginalQLayout.rankCap R u ≤ (request R u J).inputPacketRankCap ∧
    (2 : ℝ) ^ (((request R u J).order : ℝ) + 1 - (request R u J).eta) ≤
      (request R u J).inheritedConstant :=
  ActualOriginalQRequest.limits R u J

variable (A : NumericSchedule R.family J)
    (d : LocalFormal.Datum R.family (Stock.census V))
    (Q : MS.Land.Prescription B)
    (o : V → Site (R.family.side (d.level + 1) d.period))
    (μ : ℝ) (orders : V → ℕ)

def packets :=
  ActualOriginalQStartupAction.packets (J := request R u J) (datum := d)
    Q (pointDatum R J d.period (d.level + 1) o) u μ orders rfl

def colors :=
  ActualOriginalQStartupAction.colors (J := request R u J) (datum := d)
    Q (pointDatum R J d.period (d.level + 1) o) u μ orders
    (schedule R u J A) rfl

/-- The initial action has a concrete native test Datum and no added
rank-cap, palette, test-space equality or vacuum hypothesis. -/
theorem eventually_action (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (d : LocalFormal.Datum R.family (Stock.census V)), d.level = m →
      ∀ (Q : MS.Land.Prescription B)
        (o : V → Site (R.family.side (d.level + 1) d.period))
        (μ : ℝ) (orders : V → ℕ), A.inputWidth d.level ≤ 1 →
        InputColors (colors R u J A d Q o μ orders) (packets R u J d Q o μ orders) ∧
        Nonempty (FineWholeAction (request R u J) d
          (colors R u J A d Q o μ orders)
          (ActualOriginalQStartupAction.layers R (request R u J)
            (schedule R u J A) d)) := by
  filter_upwards [ActualOriginalQStartupAction.eventually_action R hG
    (request R u J) (schedule R u J A) (limits R u J).1] with m hm
  intro d hd Q o μ orders hw
  exact hm d hd (d.level + 1) le_rfl Q
    (pointDatum R J d.period (d.level + 1) o) u μ orders rfl hw

end YM.Integration.ActualOriginalQPointSetup
end
