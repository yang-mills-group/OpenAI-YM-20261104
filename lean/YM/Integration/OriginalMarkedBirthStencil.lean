import YM.Integration.ActualOriginalQInitialInput
import YM.Integration.FullQLocalFixedRadiusScaling

/-! A single original support stencil controls the actual normalized physical
Q packet for every cutoff, measurement period, fee clock and source placement. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedBirthStencil
open Function Finset Lattice Wilson RG Marker FVA1 PhysicalNext.Repeat.Legato
open LocalComparison FullQLocal FullQLocal.RenderedStep
open scoped Classical BigOperators

/-- The auxiliary covering mesh for counting faces of a physical source.
The physical mask continues to use the threshold of its incoming Run. -/
def mesh : BudgetPoint where
  power := 2
  order := 6
  supportExponent := 1
  B := 1
  threshold := 1
  power_ge := le_rfl
  order_ge := le_rfl
  exponent_pos := zero_lt_one
  B_pos := Nat.zero_lt_one
  threshold_pos := zero_lt_one
  threshold_le := le_rfl

variable {G : Gauge} {B : MS.Local.Physical.Deck G} {V : Type} [Fintype V] [DecidableEq V]
  (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B) (J : Request V)
  (A : NumericSchedule R.family J) (d : LocalFormal.Datum R.family (Stock.census V))
  (Q : MS.Land.Prescription B) (o : V → Site (R.family.side (d.level+1) d.period))
  (μ : ℝ) (orders : V → ℕ)
local notation "D" => ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
local notation "S" => ActualOriginalQInitialInput.schedule R hG u J A
local notation "M" => ActualOriginalQInitialInput.packets R hG u J A d Q o μ orders
local notation "clock" => μ-R.family.S.scale d.cutoff
local notation "offset" q:max => ActualOriginalQPackets.packetCover Q (D) u (clock) orders d.cutoff q

/-- The very same normalized marked fields have unit total price on any
covering mesh. Every true physical coefficient keeps its original coupling. -/
theorem paid (q : BudgetPoint) (g : ℝ) :
    (M).Paid q (ActualOriginalQPackets.positions (D) u).stub
      (ActualRunQlocalNativeTuple.readerRegion (D)) (fun _=>1) g ((S).inputWidth d.level)
      1 (offset q) 0 := by
  let P := ActualOriginalQFrozenInput.packets Q (D) u (clock) orders d.cutoff
  let H := ActualOriginalQInitialInput.normalizer R hG u J A d Q o μ orders
  have raw := ActualOriginalQFrozenInput.packets_paid Q (D) u (clock) orders d.cutoff g q
    (fun _=>1) ((S).inputWidth d.level) ((S).input_width_pos _) (fun _=>zero_lt_one)
  have cost : ActualOriginalQPackets.packetCost Q (D) u (clock) orders d.cutoff
      (fun _=>1) ((S).inputWidth d.level) ≤ H := by
    rw [ActualOriginalQCharges.packet_cost (D) u Q (clock) orders d.cutoff d.below
      (fun _=>1) ((S).inputWidth d.level)]
    exact le_max_right _ _
  exact FixedRadiusScaling.paid_normalized P raw H (le_max_left _ _) cost

/-- The cover of the submitted original physical token on that mesh has
a single bound fixed before every period, cutoff, root and fee clock. -/
theorem covered (q : BudgetPoint) : offset q ≤ ActualOriginalQPointCover.bound R u :=
  ActualOriginalQPointCover.packet_cover R u d.period (d.level+1) o
    (fun i=>(J.tests i).D) (fun _=>0) Q (clock) orders d.cutoff q

end YM.Integration.OriginalMarkedBirthStencil
end
