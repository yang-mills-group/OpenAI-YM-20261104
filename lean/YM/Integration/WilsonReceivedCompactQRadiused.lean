import YM.Integration.WilsonReceivedCompactQSampling
import YM.Integration.WilsonReceivedCompactMixedSites

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCompactQRadiused
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

local notation "bins" => WilsonReceivedCompactQSampling.Placements R b per
local notation "tab" => Board (N:=N) R W fees pow wallet
local notation "g" => regulatorRun R.family N per
local notation "w" test:max r:max => WilsonSeparatedOriginalThermometerCells.weight test (cells R b per r)

def floor (simple:G.Simple) (test:Test 3) := (eventually_atTop.mp (WilsonReceivedCompactMixedSites.original R simple test)).choose

def Captured (simple:G.Simple) (T:bins→tab) : Prop :=
  ∀ (test:Test 3),floor R simple test ≤ i → ∀ r:ℝ,|r| ≤ R.family.S.a i →
    ∀ (fired:∀o,(T o).domain) (c:bins→(Stock.census (Fin 3)).Mode→ℂ)
      (money:∀o,(w test r) o≠0 → (g (i+1))^pow*(∑s,‖c o s‖) ≤ wallet),
    ∃housed:∀o,(w test r) o≠0 → Housing W.p.B 0 (T o).station.roots,
      let keep:=fun o h=>Classical.choose ((T o).station.sale (fired o) (c o) 0 (housed o h) (money o h))
      (∀o h,Paid (N:=N) R W fees 0 ((T o).station.colors (fired o) (c o)) (keep o h)) ∧
       WilsonReceivedCompactCoveredCells.Integrated (N:=N) R test (cells R b per r) W
         (fun o=>(T o).station.colors (fired o) (c o)) fees (fun _=>0) keep

/-- The original compact shape buys the true common lower housing on its reporter window. -/
theorem original (simple:G.Simple) (ib:i≤b) (live:i≤N) (old:Finset (Fin 3)) (T:bins→tab)
    (origins:∀o,(T o).station.roots=WilsonReceivedCompactMixedSites.roots R ib per old o)
    (budget:W.p=R.family.path.levels.budget i) : Captured R W fees pow wallet simple T := by
  intro test late r fit fired c money
  have covered:=Classical.choose_spec (eventually_atTop.mp (WilsonReceivedCompactMixedSites.original R simple test))
  have located (o:bins) (paid:(w test r) o≠0):Nonempty (Housing W.p.B 0 (T o).station.roots) := by
    rw [budget,origins]
    exact covered i late b per ib r fit old o paid
  let house:=fun o h=>Classical.choice (located o h)
  exact ⟨house,WilsonReceivedCompactQSampling.original R W fees pow wallet live T r test fired c (fun _=>0) house money⟩

end YM.Integration.WilsonReceivedCompactQRadiused
