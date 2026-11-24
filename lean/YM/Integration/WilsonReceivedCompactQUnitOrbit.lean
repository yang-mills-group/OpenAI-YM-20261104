import YM.Integration.WilsonReceivedCompactQUnitLedger
import YM.Integration.WilsonReceivedCloseQNullProgram
import YM.Integration.WilsonReceivedCloseCompactDualStations
import YM.Integration.WilsonReceivedCompactQOrbitSites
import YM.Integration.WilsonReceivedCompactQRadiused
import YM.Integration.WilsonReceivedCompactQHardSampling
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCompactQUnitOrbit
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

/-- The jointly paid relative test keeps its signed source, true earlier winding comparison, and entire null return on one housing. -/
def Tracked (hi:b+n ≤ j) (simple:G.Simple) (T:bins → Board (N:=N) R (Ψ (b+n)) fees pow wallet) :Prop :=
  ∀ (test:Test 3),WilsonReceivedCompactQRadiused.floor R simple test ≤ b+n → ∀r:ℝ,|r| ≤ R.family.S.a (b+n) →
    ∀ (y:Site (R.family.side (b+n) per)) (fired:∀o,(T o).domain) (c:bins → (J₀).Mode → ℂ),
    let χ:=WilsonReceivedCompactQOrbitSites.sample R hi per r y
    let w:=WilsonSeparatedOriginalThermometerCells.weight test χ
    ∀money:∀o,w o≠0 → (g (b+n+1))^pow*(∑s,‖c o s‖) ≤ wallet,
    ∃housed:∀o,w o≠0 → Housing (Ψ (b+n)).p.B y (T o).station.roots,
    let keep:=fun o a=>Classical.choose ((T o).station.sale (fired o) (c o) y (housed o a) (money o a))
    let vals:=fun o=>(T o).station.colors (fired o) (c o)
    ((∀o a,Paid (N:=N) R (Ψ (b+n)) fees y (vals o) (keep o a)) ∧
       WilsonReceivedCompactCoveredCells.Integrated (N:=N) R test χ (Ψ (b+n)) vals fees (fun _=>y) keep) ∧
    WilsonReceivedCompactQUnitLedger.Integrated (N:=N) R Ψ test χ b n ε fees y vals keep

include course in
theorem original (simple:G.Simple) (lo:m ≤ b) (hi:b+n ≤ j) (live:j ≤ N) (ep:0 ≤ ε)
    (old:Finset (Fin 3)) (T:bins → Board (N:=N) R (Ψ (b+n)) fees pow wallet)
    (sites:∀o,(T o).station.roots=WilsonReceivedCompactMixedSites.roots R hi per old o)
    (gates:WilsonReceivedCloseQNullProgram.Gates R N per m j Ψ ε) :
    Tracked R Ψ b n ε fees pow wallet hi simple T := by
  intro test late r fit y fired c
  dsimp only
  intro money
  let χ:=WilsonReceivedCompactQOrbitSites.sample R hi per r y
  let w:=WilsonSeparatedOriginalThermometerCells.weight test χ
  have measured:=WilsonReceivedCompactQOrbitSites.measurable R hi per r y
  have anchored (o:bins) (a:w o≠0):Nonempty (Housing (Ψ (b+n)).p.B y (T o).station.roots) := by
    have point:=(course.1.walk (b+n) (by omega) (hi.trans live)).truep.point
    rw [point,sites]
    exact WilsonReceivedCompactQOrbitSites.original R hi per simple test late r fit y old o a
  let house:=fun o a=>Classical.choice (anchored o a)
  let keep:=fun o a=>Classical.choose ((T o).station.sale (fired o) (c o) y (house o a) (money o a))
  have bought o a:=Classical.choose_spec ((T o).station.sale (fired o) (c o) y (house o a) (money o a))
  refine ⟨house,WilsonReceivedCloseCompactStations.compact R (hi.trans live) (Ψ (b+n)) test χ measured fees pow wallet
    (fun o=>(T o).station) fired c (fun _=>y) house money,?_⟩
  apply WilsonReceivedCompactQUnitLedger.original R π Γ Ψ course test χ measured b n ε fees y
    (fun o=>(T o).station.colors (fired o) (c o)) keep lo (hi.trans live) ep bought
  · intro o a
    exact (gates (b+n) (by omega) hi).2 fees y _ _ (bought o a)
  · intro i time origin
    exact (gates (b+i) (by omega) (by omega)).1 origin

/-- One physical board, with its single elected sale, serves every possible earlier stop in the paid interval. -/
def Stops (i:ℕ) (ib:i ≤ j) (simple:G.Simple) (T:bins → Board (N:=N) R (Ψ i) fees pow wallet) :Prop :=
  ∀ b n, m ≤ b → ∀same:b+n=i,
    Tracked (N:=N) R Ψ b n ε fees pow wallet (same.le.trans ib) simple (same.symm ▸ T)

include course in
theorem stops (i:ℕ) (simple:G.Simple) (ib:i ≤ j) (live:j ≤ N) (ep:0 ≤ ε) (old:Finset (Fin 3))
    (T:bins → Board (N:=N) R (Ψ i) fees pow wallet)
    (sites:∀o,(T o).station.roots=WilsonReceivedCompactMixedSites.roots R ib per old o)
    (gates:WilsonReceivedCloseQNullProgram.Gates R N per m j Ψ ε) :
    Stops (N:=N) (m:=m) R Ψ ε fees pow wallet i ib simple T := by
  intro b n lo same
  subst i
  exact original R π Γ Ψ course b n ε fees pow wallet simple lo ib live ep old T sites gates

end YM.Integration.WilsonReceivedCompactQUnitOrbit
