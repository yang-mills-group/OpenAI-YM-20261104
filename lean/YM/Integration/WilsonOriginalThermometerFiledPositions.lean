import YM.Integration.WilsonReceivedCloseHistory
import YM.Next.RANK.Coordinates

noncomputable section
namespace YM.Integration.WilsonReceivedCloseHistory
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open scoped BigOperators

variable {G : Gauge} (R : Run G) {m b N per k : ℕ}
  (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D : Roots (G := G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ  →  Layout G) (Γ : ℕ  →  Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ  →  ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V  →  Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V  →  ℕ)
  (order shelf seats : ℕ) (mb : m  ≤  b)
  (source : Wallet actors  →  Config G (R.family.side (b+1) per)  →  Poly (Stock.census V))

local notation "carrier" i : max f:max y : max => Post (N := N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y


/-- Follow each actual registered child on the filed history of the full source. -/
theorem Trail.positions (P₀ : carrier b mb source) {i :  ℕ} {floor :  m  ≤  i}
    {y :  Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)}
    {L : carrier i floor y} (invoice : Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source P₀ i floor y L) (origin :  V  →  Site (R.family.side N per)) (top : b+1 ≤ N)
    (begins : ∀v,P₀.passport.origin v=(R.family.S.toDepth top per).parent (origin v)):
    ∃ stopped : i+1  ≤  N, ∀ v, L.passport.origin v=(R.family.S.toDepth stopped per).parent (origin v)  :=  by
  induction invoice with
  | start => exact ⟨top,begins⟩
  | @step j floor y U L earlier filed factor active paid wages previous =>
    obtain ⟨upper,same⟩ := previous
    refine ⟨(Nat.le_succ _).trans upper,fun v => ?_⟩
    rw [filed.passport]
    change (R.family.path.levels.clock.op (j+1) per).ratio.parent (U.passport.origin v)=_
    rw [same]
    exact (Next.Rank.Station.parent_nested (R.family.path.levels.clock.op (j+1) per).ratio
      (R.family.S.toDepth upper per) _ (R.family.S.block_odd _) (R.family.S.toDepth_odd upper per)
      (origin v)).symm

end YM.Integration.WilsonReceivedCloseHistory
