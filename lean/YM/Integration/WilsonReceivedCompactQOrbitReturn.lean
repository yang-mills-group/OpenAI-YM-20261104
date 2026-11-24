import YM.Integration.WilsonReceivedCloseCompactDualStations
import YM.Integration.WilsonReceivedCompactQOrbitSites
import YM.Integration.WilsonReceivedCompactQRadiused
import YM.Integration.WilsonReceivedCompactQHardSampling
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCompactQOrbitReturn
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


def Captured (ib:i+1≤b) (simple:G.Simple) (T:bins → tab):Prop :=
  ∀(test:Test 3),WilsonReceivedCompactQRadiused.floor R simple test ≤ i+1 → ∀r:ℝ,|r| ≤ R.family.S.a (i+1) →
  ∀ (center:Site (R.family.side (i+1) per)) (fired:∀o,(T o).upper.domain) (c:bins → (Stock.census (Fin 3)).Mode → ℂ)
    (money:∀o,(WilsonSeparatedOriginalThermometerCells.weight test (WilsonReceivedCompactQOrbitSites.sample R ib per r center)) o≠0 → (g (i+1+1))^pow*(∑s,‖c o s‖) ≤ wallet),
    ∃housed:∀o,(WilsonSeparatedOriginalThermometerCells.weight test (WilsonReceivedCompactQOrbitSites.sample R ib per r center)) o≠0 → Housing (Ψ (i+1)).p.B center (T o).upper.station.roots,
    let keep:=fun o h=>Classical.choose ((T o).upper.station.sale (fired o) (c o) center (housed o h) (money o h))
    ((∀o a,Paid (N:=N) R (Ψ (i+1)) fees center ((T o).upper.station.colors (fired o) (c o)) (keep o a)) ∧
       WilsonReceivedCompactCoveredCells.Integrated (N:=N) R test (WilsonReceivedCompactQOrbitSites.sample R ib per r center) (Ψ (i+1))
         (fun o=>(T o).upper.station.colors (fired o) (c o)) fees (fun _=>center) keep) ∧
    let returnAt:=fun o h=>(T o).settle (fired o) (c o) center (housed o h) (money o h)
    let older:=fun o h=>Classical.choose (returnAt o h)
    let paid:=fun o h=>Classical.choose (Classical.choose_spec (returnAt o h))
    (∀o a,WilsonReceivedCompactPlacedStep.Returned (N:=N) R Ψ center (keep o a) (older o a) (paid o a) fees.regular) ∧
    WilsonReceivedCompactPlacedStep.Integrated (N:=N) R Ψ test (WilsonReceivedCompactQOrbitSites.sample R ib per r center) (fun _=>center) fees.regular keep older paid

include course in
theorem original (simple:G.Simple) (ib:i+1 ≤ b) (begun:m ≤ i+1) (live:i+1 ≤ N) (old:Finset (Fin 3))
    (T:bins → tab) (origins:∀o,(T o).upper.station.roots=WilsonReceivedCompactMixedSites.roots R ib per old o)
    (budget:(Ψ (i+1)).p=R.family.path.levels.budget (i+1)) : Captured R Ψ fees pow wallet ib simple T := by
  intro test late r fit center fired c money
  let χ:=WilsonReceivedCompactQOrbitSites.sample R ib per r center
  have measure:=WilsonReceivedCompactQOrbitSites.measurable R ib per r center
  let w:=WilsonSeparatedOriginalThermometerCells.weight test χ
  have located (o:bins) (paid:w o≠0):Nonempty (Housing (Ψ (i+1)).p.B center (T o).upper.station.roots) := by
    rw [budget,origins]
    exact WilsonReceivedCompactQOrbitSites.original R ib per simple test late r fit center old o paid
  let house:=fun o h=>Classical.choice (located o h)
  let keep:=fun o h=>Classical.choose ((T o).upper.station.sale (fired o) (c o) center (house o h) (money o h))
  let returnAt:=fun o h=>(T o).settle (fired o) (c o) center (house o h) (money o h)
  let older:=fun o h=>Classical.choose (returnAt o h)
  let paid:=fun o h=>Classical.choose (Classical.choose_spec (returnAt o h))
  have posted (o a):WilsonReceivedCompactPlacedStep.Returned (N:=N) R Ψ center (keep o a) (older o a) (paid o a) fees.regular:=
    Classical.choose_spec (Classical.choose_spec (returnAt o a))
  have issued (o a):=Classical.choose_spec ((T o).upper.station.sale (fired o) (c o) center (house o a) (money o a))
  refine ⟨house,WilsonReceivedCloseCompactStations.compact R live (Ψ (i+1)) test χ measure fees pow wallet
    (fun o=>(T o).upper.station) fired c (fun _=>center) house money,posted,?_⟩
  exact WilsonReceivedCompactPlacedStep.original R π Γ Ψ course test χ measure begun live (fun _=>center) fees.regular
    keep (fun o a=>(issued o a).1) (fun o a=>(issued o a).2.1) older paid posted

end YM.Integration.WilsonReceivedCompactQOrbitReturn
