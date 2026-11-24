import YM.Integration.WilsonOriginalThermometerFiledPositions

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



/-- The original point passport used by the common top enrollment starts the
full filed history with the three literal upper sites. -/
theorem Trail.fromTop (P₀ : Post (N:=b+1) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats b mb source)
    {i : ℕ} {floor : m ≤ i}
    {y : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)}
    {L : Post (N:=b+1) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i floor y}
    (invoice : Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source P₀ i floor y L)
    (v : V → Site (R.family.side (b+1) per)) (register : P₀.passport=Earn.Passport.point v) :
    ∃ passed : i+1 ≤ b+1, ∀ u,
      L.passport.origin u=(R.family.S.toDepth passed per).parent (v u) := by
  apply Trail.positions R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb source P₀ invoice v le_rfl
  intro u
  rw [register]
  change v u = (R.family.S.toDepth (le_refl (b+1)) per).parent (v u)
  let r:=R.family.S.toDepth (le_refl (b+1)) per
  have gone : r.embed (v u)=v u := r.embed_injective ((Next.Rank.Station.embed_comp r r r _).symm)
  exact (r.embed_parent _).symm.trans (congrArg r.parent gone)

end YM.Integration.WilsonReceivedCloseHistory
