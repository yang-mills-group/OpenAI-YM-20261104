import YM.Integration.WilsonOriginalThermometerFiledPositions

noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialHomes
open WilsonReceivedCloseHistory
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



theorem received (P₀:carrier b mb source) {i:ℕ} {floor:m ≤ i}
    {y:Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)}
    {L:carrier i floor y}
    (tr:Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source P₀ i floor y L)
    (upper:b+1 ≤ N) (age:i ≤ b) (o:V → Site (R.family.side i per))
    (starts:∀v,P₀.passport.origin v=(R.family.S.toDepth (age.trans (Nat.le_succ b)) per).embed (o v)):
    ∀v,(L.passport.coarser (R.family.path.levels.clock.op i per).ratio).origin v=o v:=by
  let a:=R.family.S.toDepth (age.trans (Nat.le_succ b)) per
  let b':=R.family.S.toDepth upper per
  let r:=R.family.S.toDepth ((age.trans (Nat.le_succ b)).trans upper) per
  have start(v:V):P₀.passport.origin v=b'.parent (r.embed (o v)):=by
    rw [starts,Next.Rank.Station.embed_comp a b' r,b'.embed_parent]
  obtain ⟨live,homes⟩:=Trail.positions R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb
    source P₀ tr (fun v=>r.embed (o v)) upper start
  intro v
  let c:=(R.family.path.levels.clock.op i per).ratio
  let u:=R.family.S.toDepth live per
  change c.parent (L.passport.origin v)=o v
  rw [homes]
  exact (Next.Rank.Station.parent_nested c u r (R.family.S.block_odd _) (R.family.S.toDepth_odd live per)
    (r.embed (o v))).symm.trans (r.embed_parent _)

end YM.Integration.WilsonOriginalAlternativeTrialHomes
