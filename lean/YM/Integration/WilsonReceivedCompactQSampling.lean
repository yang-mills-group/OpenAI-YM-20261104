import YM.Integration.WilsonReceivedCloseCompactStations

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCompactQSampling
open Filter Finset Multi Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra Source
open FullQLocal FullQLocal.RenderedStep Multi Exterior Comparison.RG02.Cumulants
open OPE.Therm WilsonLimitConstruction RG16.Literal Source Labels Extra.Histories
open scoped BigOperators Classical

open WilsonReceivedGeometricCellReadout RG16.Literal Next.Foundations MeasureTheory XSpace XSpace.Rose OPE.Orbits
open WilsonReceivedCloseCompactStations WilsonReceivedCompactPriorIntegral
variable {G:Gauge} (R:Run G) {N per i b:ℕ} (W:Rep G (R.family.side i per)) (fees:Fares) (pow:ℕ) (wallet:ℝ)

abbrev Placements (b per:ℕ) := ((Fin 3)→Site (R.family.side ((b+1)+1) per)) × ((Fin 3)→Site (R.family.side (b+1) per))
local notation "bins" => Placements R b per
local notation "tab" => Board (N:=N) R W fees pow wallet
local notation "g" => regulatorRun R.family N per
local notation "w" test:max r:max => WilsonSeparatedOriginalThermometerCells.weight test (cells R b per r)

/-- Each registered child is evaluated in its own microscopic cell at its actual birth, with the original signed shape. -/
def Tested (T:bins→tab) : Prop :=
  ∀ (r:ℝ) (test:Test 3) (fired:∀o,(T o).domain) (c:bins→(Stock.census (Fin 3)).Mode→ℂ)
    (y:bins→Site (R.family.side i per)) (housed:∀o,(w test r) o≠0 → Housing W.p.B (y o) (T o).station.roots)
    (money:∀o,(w test r) o≠0 → (g (i+1))^pow*(∑s,‖c o s‖) ≤ wallet),
    let keep:=fun o h=>Classical.choose ((T o).station.sale (fired o) (c o) (y o) (housed o h) (money o h))
    (∀o h,Paid (N:=N) R W fees (y o) ((T o).station.colors (fired o) (c o)) (keep o h)) ∧
     WilsonReceivedCompactCoveredCells.Integrated (N:=N) R test (cells R b per r) W
       (fun o=>(T o).station.colors (fired o) (c o)) fees y keep

theorem original (live:i ≤ N) (T:bins→tab):Tested R W fees pow wallet T:=by
  intro r test fired c y housed money
  exact WilsonReceivedCloseCompactStations.compact R live W test (cells R b per r)
    (measurable_cells R b per r) fees pow wallet (fun o=>(T o).station) fired c y housed money

end YM.Integration.WilsonReceivedCompactQSampling
