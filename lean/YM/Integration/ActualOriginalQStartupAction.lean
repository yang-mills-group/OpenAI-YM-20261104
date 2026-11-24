import YM.Integration.ActualOriginalQFrozenInput
import YM.Integration.NativePaidPacketColors
import YM.Integration.ActualStartupAdmittedAlbum
import YM.Integration.ActualLayerFineAction

/-! The original startup album supplies the Grade5 vacuum for the frozen
original-Q source. The same native path and all album rows remain. The
admitted-album tail precedes all periods, Q columns and test tuples.
This constructs the action component, not packet-cost or cover admission. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalQStartupAction
open Function Filter Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global
open Comparison.RG02 Comparison.RG02.Assembly
open IterationFour IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders
open scoped Classical BigOperators Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]

def layers (R : Run G) (J : Request V) (A : NumericSchedule R.family J)
    (datum : LocalFormal.Datum R.family (Stock.census V)) :=
  ActualStartupInvoice.paidAlbum G (R.family.side (datum.level + 1) datum.period)
    (A.inputNorm datum.level) (R.family.path.levels.params (datum.level + 1))
    J.order (A.inputWidth datum.level)

private theorem reindex_input {n : Side} {S : Census V}
    {D E : V → ComparisonDensity.Address.Orbit} (h : E = D)
    (P : MarkedPackets D G n S)
    (c : TestSpace D → Bulk.Colors S G n) (hc : InputColors c P) :
    InputColors (fun x => c (h ▸ x)) (h.symm ▸ P) := by
  cases h
  exact hc

variable {R : Run G} {B : MS.Local.Physical.Deck G}
    {J : Request V} {datum : LocalFormal.Datum R.family (Stock.census V)}
    {n : ℕ} {hn : n ≤ datum.level + 1}
    (Q : MS.Land.Prescription B)
    (D : ActualRunQlocalNativeTuple.Datum R datum.period (datum.level + 1) n hn V)
    (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)

def packets (hTests : J.tests = ActualRunQlocalNativeTuple.orbit D) :
    MarkedPackets J.tests G (R.family.side (datum.level + 1) datum.period)
      (Stock.census V) :=
  hTests.symm ▸ ActualOriginalQFrozenInput.packets Q D u μ orders datum.cutoff

def colors (A : NumericSchedule R.family J)
    (hTests : J.tests = ActualRunQlocalNativeTuple.orbit D) :
    TestSpace J.tests → Bulk.Colors (Stock.census V) G
      (R.family.side (datum.level + 1) datum.period) :=
  fun x => NativePaidPacketColors.colors
    (ActualOriginalQFrozenInput.packets Q D u μ orders datum.cutoff)
    (ActualGradedVacuum.restored (layers R J A datum)) (hTests ▸ x)

private theorem paid_one (point : BudgetPoint) :
    (ActualOriginalQFrozenInput.packets Q D u μ orders datum.cutoff).Paid
      point (ActualOriginalQPackets.positions D u).stub
      (ActualRunQlocalNativeTuple.readerRegion D) (fun _ => 1) 1 1
      (ActualOriginalQPackets.packetCost Q D u μ orders datum.cutoff (fun _ => 1) 1)
      (ActualOriginalQPackets.packetCover Q D u μ orders datum.cutoff point) 0 :=
  ActualOriginalQFrozenInput.packets_paid Q D u μ orders datum.cutoff 1
    point (fun _ => 1) 1 (by norm_num) (fun _ => by norm_num)

variable {A : NumericSchedule R.family J}
    (H : GradedVacuumLayers (layers R J A datum) (A.inputNorm datum.level)
      J.order J.vacuumRankCap (A.inputWidth datum.level) (A.admittedCost datum.level))

include H in
/-- The actual paid album supplies all vacuum conditions for this Q source. -/
theorem input_colors (hTests : J.tests = ActualRunQlocalNativeTuple.orbit D) :
    InputColors (colors (datum := datum) Q D u μ orders A hTests)
      (packets (datum := datum) Q D u μ orders hTests) := by
  have hc := NativePaidPacketColors.input_colors
    (paid_one (datum := datum) Q D u μ orders (A.inputNorm datum.level)) one_ne_zero
    (ActualGradedVacuum.restored (layers R J A datum))
    ((ActualGradedVacuum.restored_grade H (A.input_width_pos datum.level)).lower
      (by decide : 3 ≤ 5))
    (ActualGradedVacuum.restored_gauge H)
    (ActualGradedVacuum.restored_envelope H (A.input_width_pos datum.level))
  exact reindex_input hTests _ _ hc

include H in
/-- This is the original startup path plus the same paid layer list, with
one analytic action extension before every independent test tuple. -/
theorem whole_action (hTests : J.tests = ActualRunQlocalNativeTuple.orbit D) :
    Nonempty (FineWholeAction J datum (colors (datum := datum) Q D u μ orders A hTests)
      (layers R J A datum)) :=
  ActualLayerFineAction.whole_action R (Stock.census V) J datum H
    (A.input_width_pos datum.level) (colors (datum := datum) Q D u μ orders A hTests)
    (packets (datum := datum) Q D u μ orders hTests)
    (input_colors (datum := datum) Q D u μ orders H hTests) (fun _ => rfl)

/-- The original admitted-album theorem constructs H on one tail. No
graded-vacuum or analytic-color hypothesis is added to this conclusion.
The selected width/rank conditions remain the genuine schedule duties. -/
theorem eventually_action (R : Run G) (hG : G.Simple) (J : Request V)
    (A : NumericSchedule R.family J) (hrank : J.order + 2 ≤ J.vacuumRankCap) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum R.family (Stock.census V)),
        datum.level = m →
      ∀ (n : ℕ) (hn : n ≤ datum.level + 1)
        (Q : MS.Land.Prescription B)
        (D : ActualRunQlocalNativeTuple.Datum R datum.period (datum.level + 1) n hn V)
        (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)
        (hTests : J.tests = ActualRunQlocalNativeTuple.orbit D),
        A.inputWidth datum.level ≤ 1 →
        InputColors (colors (datum := datum) Q D u μ orders A hTests)
          (packets (datum := datum) Q D u μ orders hTests) ∧
        Nonempty (FineWholeAction J datum (colors (datum := datum) Q D u μ orders A hTests)
          (layers R J A datum)) := by
  filter_upwards [ActualStartupAdmittedAlbum.eventually_paid_layers R hG J A hrank]
    with m hm
  intro datum hlevel n hn Q D u μ orders hTests hwidth
  subst m
  obtain ⟨H⟩ := hm datum.period hwidth
  exact ⟨input_colors (datum := datum) Q D u μ orders H hTests,
    whole_action (datum := datum) Q D u μ orders H hTests⟩

end YM.Integration.ActualOriginalQStartupAction
end
