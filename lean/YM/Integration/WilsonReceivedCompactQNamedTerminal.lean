import YM.Integration.WilsonReceivedCompactQCoveredStop
import YM.Integration.WilsonReceivedCloseQUnitFunding

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCompactQNamedTerminal
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
variable {G:Gauge} (R:Run G) {m N per k j:ℕ}
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀i,RG.Rep G (R.family.side i per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (b n:ℕ) (ε:ℝ) (fees:Fares) (pow:ℕ) (wallet:ℝ)
local notation "bins" => WilsonReceivedCompactQSampling.Placements R j per
local notation "J₀" => Stock.census (Fin 3)
local notation "g" i:max => Coat.gStep (R.family.path.β N per i)

/-- The hard account and all actual unit feeds are tested on the very same physical sale already recorded for the orbit. -/
def AtStop (hi:b+n ≤ j) (simple:G.Simple) (T:bins → Board (N:=N) R (Ψ (b+n)) fees pow wallet)
    (held:WilsonReceivedCompactQUnitOrbit.Tracked (N:=N) R Ψ b n ε fees pow wallet hi simple T) :Prop :=
  ∀ (test:Test 3) (late:WilsonReceivedCompactQRadiused.floor R simple test ≤ b+n) (r:ℝ) (fit:|r| ≤ R.family.S.a (b+n))
    (y:Site (R.family.side (b+n) per)) (fired:∀o,(T o).domain) (c:bins → (J₀).Mode → ℂ),
    let χ:=WilsonReceivedCompactQOrbitSites.sample R hi per r y
    let w:=WilsonSeparatedOriginalThermometerCells.weight test χ
    ∀money:∀o,w o≠0 → (g (b+n+1))^pow*(∑s,‖c o s‖) ≤ wallet,
    let visit:=held test late r fit y fired c money
    let housed:=Classical.choose visit
    let keep:=fun o a=>Classical.choose ((T o).station.sale (fired o) (c o) y (housed o a) (money o a))
    WilsonReceivedCompactQUnitTerminal.Signed (N:=N) R Ψ test χ b n ε fees y
      (fun o=>(T o).station.colors (fired o) (c o)) keep (Classical.choose_spec visit).2 ∧
    WilsonReceivedCompactQCoveredStop.Earlier (N:=N) R Ψ test χ b n ε fees y
      (fun o=>(T o).station.colors (fired o) (c o)) keep (Classical.choose_spec visit).2

include course in
theorem original (hi:b+n ≤ j) (simple:G.Simple) (T:bins → Board (N:=N) R (Ψ (b+n)) fees pow wallet)
    (held:WilsonReceivedCompactQUnitOrbit.Tracked (N:=N) R Ψ b n ε fees pow wallet hi simple T)
    (start:m ≤ b) (live:j ≤ N) (ep:0 ≤ ε) (cofinal:WilsonReceivedQUnitCompulsory.onset R simple ≤ b) :
    AtStop (N:=N) R Ψ b n ε fees pow wallet hi simple T held := by
  intro test late r fit y fired c
  dsimp only
  intro money
  let χ:=WilsonReceivedCompactQOrbitSites.sample R hi per r y
  let visit:=held test late r fit y fired c money
  have stopped:=WilsonReceivedCompactQUnitTerminal.original R π Γ Ψ course test χ b n ε fees y
    (fun o=>(T o).station.colors (fired o) (c o)) simple (WilsonReceivedCompactQOrbitSites.measurable R hi per r y)
    _ (Classical.choose_spec visit).2 start (hi.trans live) ep cofinal
  exact ⟨stopped, WilsonReceivedCompactQCoveredStop.original R π Γ Ψ course test χ b n ε fees y
    (fun o=>(T o).station.colors (fired o) (c o)) simple (WilsonReceivedCompactQOrbitSites.measurable R hi per r y)
    _ (Classical.choose_spec visit).1.1 (Classical.choose_spec visit).2 stopped start (hi.trans live)⟩

def Ages (i:ℕ) (ib:i ≤ j) (simple:G.Simple) (T:bins → Board (N:=N) R (Ψ i) fees pow wallet)
    (all:WilsonReceivedCompactQUnitOrbit.Stops (N:=N) (m:=m) R Ψ ε fees pow wallet i ib simple T) :Prop :=
  ∀b n (lo:m ≤ b) (same:b+n=i),AtStop (N:=N) R Ψ b n ε fees pow wallet (same.le.trans ib) simple
    (same.symm ▸ T) (all b n lo same)

include course in
theorem ages (i:ℕ) (ib:i ≤ j) (simple:G.Simple) (T:bins → Board (N:=N) R (Ψ i) fees pow wallet)
    (all:WilsonReceivedCompactQUnitOrbit.Stops (N:=N) (m:=m) R Ψ ε fees pow wallet i ib simple T)
    (live:j ≤ N) (ep:0 ≤ ε) (cofinal:WilsonReceivedQUnitCompulsory.onset R simple ≤ m) :
    Ages (N:=N) (m:=m) R Ψ ε fees pow wallet i ib simple T all := by
  intro b n lo same
  subst i
  exact original R π Γ Ψ course b n ε fees pow wallet ib simple T (all b n lo rfl) lo live ep (cofinal.trans lo)

end YM.Integration.WilsonReceivedCompactQNamedTerminal
