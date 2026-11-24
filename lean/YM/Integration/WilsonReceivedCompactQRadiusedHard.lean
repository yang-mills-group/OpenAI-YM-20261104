import YM.Integration.WilsonReceivedCloseCompactDualStations
import YM.Integration.WilsonReceivedCompactQRadiused
import YM.Integration.WilsonReceivedCompactQHardSampling
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCompactQRadiusedHard
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

def Captured (simple:G.Simple) (T:bins → tab):Prop :=
  ∀(test:Test 3),WilsonReceivedCompactQRadiused.floor R simple test ≤ i+1 → ∀r:ℝ,|r| ≤ R.family.S.a (i+1) →
  ∀ (fired:∀o,(T o).upper.domain) (c:bins → (Stock.census (Fin 3)).Mode → ℂ)
    (money:∀o,(w test r) o≠0 → (g (i+1+1))^pow*(∑s,‖c o s‖) ≤ wallet),
    ∃housed:∀o,(w test r) o≠0 → Housing (Ψ (i+1)).p.B 0 (T o).upper.station.roots,
    let keep:=fun o h=>Classical.choose ((T o).upper.station.sale (fired o) (c o) 0 (housed o h) (money o h))
    ((∀o a,Paid (N:=N) R (Ψ (i+1)) fees 0 ((T o).upper.station.colors (fired o) (c o)) (keep o a)) ∧
       WilsonReceivedCompactCoveredCells.Integrated (N:=N) R test (cells R b per r) (Ψ (i+1))
         (fun o=>(T o).upper.station.colors (fired o) (c o)) fees (fun _=>0) keep) ∧
    let returnAt:=fun o h=>(T o).settle (fired o) (c o) 0 (housed o h) (money o h)
    let older:=fun o h=>Classical.choose (returnAt o h)
    let paid:=fun o h=>Classical.choose (Classical.choose_spec (returnAt o h))
    (∀o a,WilsonReceivedCompactPlacedStep.Returned (N:=N) R Ψ 0 (keep o a) (older o a) (paid o a) fees.regular) ∧
    WilsonReceivedCompactPlacedStep.Integrated (N:=N) R Ψ test (cells R b per r) (fun _=>0) fees.regular keep older paid

include course in
theorem original (simple:G.Simple) (ib:i+1 ≤ b) (begun:m ≤ i+1) (live:i+1 ≤ N) (old:Finset (Fin 3))
    (T:bins → tab) (origins:∀o,(T o).upper.station.roots=WilsonReceivedCompactMixedSites.roots R ib per old o)
    (budget:(Ψ (i+1)).p=R.family.path.levels.budget (i+1)) : Captured R Ψ fees pow wallet simple T := by
  intro test late r fit fired c money
  have covered:=Classical.choose_spec (eventually_atTop.mp (WilsonReceivedCompactMixedSites.original R simple test))
  have located (o:bins) (paid:(w test r) o≠0):Nonempty (Housing (Ψ (i+1)).p.B 0 (T o).upper.station.roots) := by
    rw [budget,origins]
    exact covered (i+1) late b per ib r fit old o paid
  let house:=fun o h=>Classical.choice (located o h)
  have issued:=WilsonReceivedCompactQHardSampling.original (b:=b) R π Γ Ψ course fees pow wallet begun live T
  exact ⟨house,issued.1 r test fired c (fun _=>0) house money,issued.2 r test fired c (fun _=>0) house money⟩

end YM.Integration.WilsonReceivedCompactQRadiusedHard
