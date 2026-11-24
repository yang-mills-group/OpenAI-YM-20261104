import YM.Integration.WilsonCapturedPrimaryTrailSites
import YM.Integration.WilsonReceivedCompactQBirthSites
import YM.Next.RANK.Coordinates

/-! The dated passport at every genuine close post tracks the submitted
sites through the original physical schedule before its local halo is tested. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedCompactQTrailSites
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Pert.Asymptotics Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter
open Extra.Histories Further.PhysicalPeriodLimitF933 Push.AbsoluteSums Planned.GuardedAtom
open scoped Classical BigOperators Topology
open Labels Source Push.Local Next.Foundations Planned.AtomRegular Trace.Physical.Germ
open RG16

variable {G : Gauge} (R : Run G) (simple : G.Simple) {m b N per k : ℕ}
  (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ i, RG.Rep G (R.family.side i per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {X : Fin 3 → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : Fin 3 → ℕ)
  (order shelf seats : ℕ) (mb : m  ≤  b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census (Fin 3)))
local notation "history" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "post" i:max f:max y:max => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y
local notation "g" => regulatorRun R.family N per
local notation "move" i:max => R.family.path.levels.clock.op i per


local notation "Sites" d:max => Fin 3 → Site (R.family.side d per)

theorem original (start:post b mb source) {i:ℕ} (ib:i ≤ b) {mi:m ≤ i}
    {Y:Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census (Fin 3))}
    {L:post i mi Y} (trail:WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces
      grades order shelf seats mb source start i mi Y L)
    (old:Finset (Fin 3)) (top:Sites ((b+1)+1)) (fine:Sites (b+1))
    (first:WilsonReceivedCompactQBirthSites.Located R old top fine start.passport) :
    (L.passport.coarser (move i).ratio).origin=WilsonReceivedCompactMixedSites.roots R ib per old (top,fine) := by
  funext v
  have marched:=WilsonCapturedPrimaryTrailSites.outgoing R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats mb source start ib trail v
  rw [marched,first v]
  unfold WilsonReceivedCompactMixedSites.roots
  split_ifs
  · exact (Next.Rank.Station.parent_nested _ _ _ (R.family.S.toDepth_odd (ib.trans (Nat.le_succ b)) per)
      (R.family.S.block_odd (b+1)) _).symm
  · rfl

end YM.Integration.WilsonReceivedCompactQTrailSites
