import YM.Integration.WilsonReceivedCloseCompactDualStations
import YM.Integration.WilsonReceivedCompactQSampling
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCompactQHardSampling
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
open WilsonReceivedCloseCompactDualStations RG16.Literal
variable {G:Gauge} (R:Run G) {N per m k i b:ℕ} (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin)
  (Ψ:∀j,RG.Rep G (R.family.side j per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (fees:Fares) (pow:ℕ) (wallet:ℝ)
local notation "bins" => WilsonReceivedCompactQSampling.Placements R b per
local notation "tab" => Dual (N:=N) R Ψ i fees pow wallet
local notation "g" => regulatorRun R.family N per
local notation "w" test:max r:max => WilsonSeparatedOriginalThermometerCells.weight test (cells R b per r)

def Tested (T:bins → tab):Prop :=
  WilsonReceivedCompactQSampling.Tested (b:=b) R (Ψ (i+1)) fees pow wallet (fun o=>(T o).upper) ∧
  ∀ (r:ℝ) (test:Test 3) (fired:∀o,(T o).upper.domain) (c:bins → (Stock.census (Fin 3)).Mode → ℂ)
    (y:bins → Site (R.family.side (i+1) per)) (housed:∀o,(w test r) o≠0 → Housing (Ψ (i+1)).p.B (y o) (T o).upper.station.roots)
    (money:∀o,(w test r) o≠0 → (g (i+1+1))^pow*(∑s,‖c o s‖) ≤ wallet),
    let keep:=fun o h=>Classical.choose ((T o).upper.station.sale (fired o) (c o) (y o) (housed o h) (money o h))
    let returnAt:=fun o h=>(T o).settle (fired o) (c o) (y o) (housed o h) (money o h)
    let older:=fun o h=>Classical.choose (returnAt o h)
    let paid:=fun o h=>Classical.choose (Classical.choose_spec (returnAt o h))
    (∀o a,WilsonReceivedCompactPlacedStep.Returned (N:=N) R Ψ (y o) (keep o a) (older o a) (paid o a) fees.regular) ∧
    WilsonReceivedCompactPlacedStep.Integrated (N:=N) R Ψ test (cells R b per r) y fees.regular keep older paid

include course in
theorem original (begun:m ≤ i+1) (live:i+1 ≤ N) (T:bins → tab) : Tested R Ψ fees pow wallet T:=by
  refine ⟨WilsonReceivedCompactQSampling.original (b:=b) R (Ψ (i+1)) fees pow wallet live (fun o=>(T o).upper),?_⟩
  intro r test fired c y housed money
  let keep:=fun o h=>Classical.choose ((T o).upper.station.sale (fired o) (c o) (y o) (housed o h) (money o h))
  let returnAt:=fun o h=>(T o).settle (fired o) (c o) (y o) (housed o h) (money o h)
  let older:=fun o h=>Classical.choose (returnAt o h)
  let paid:=fun o h=>Classical.choose (Classical.choose_spec (returnAt o h))
  have posted (o a):WilsonReceivedCompactPlacedStep.Returned (N:=N) R Ψ (y o) (keep o a) (older o a) (paid o a) fees.regular:=
    Classical.choose_spec (Classical.choose_spec (returnAt o a))
  have issued (o a):=Classical.choose_spec ((T o).upper.station.sale (fired o) (c o) (y o) (housed o a) (money o a))
  exact ⟨posted, WilsonReceivedCompactPlacedStep.original R π Γ Ψ course test (cells R b per r)
    (measurable_cells R b per r) begun live y fees.regular keep (fun o a=>(issued o a).1)
    (fun o a=>(issued o a).2.1) older paid posted⟩

end YM.Integration.WilsonReceivedCompactQHardSampling
