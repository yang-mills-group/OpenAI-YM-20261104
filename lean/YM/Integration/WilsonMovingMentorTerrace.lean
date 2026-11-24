import YM.Integration.WilsonMovingMentorConcourse
import YM.Integration.WilsonMovingMentorWarm
import YM.QuadraticLocal.Startup.Headway

/-! The true terminal hard budget and all preceding Wilson fields are selected together. -/
noncomputable section
namespace YM.Integration.WilsonMovingMentorTerrace
open Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Org Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit AllOrder.Transit.WheelP
open scoped Classical

variable {G : Gauge} (R : Run G)

theorem realized (simple : G.Simple) (bought : WilsonMovingMentorWarm.Conditions R.kit)
    {r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    {Q : r.Tab R.rolls} (funded : Pass r Q R.alloy R.kit) {k m N : ℕ}
    (rank : Burn.horizon k + 2 ≤ R.alloy.B.a.clock.J m) (live : m ≤ N)
    (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
    (path : PlanV.Path r R.alloy Q (Burn.horizon k) N m π Γ) (per : ℕ) :
    ∃ H : (i : ℕ) → RG.Rep G (R.alloy.B.a.S.side i per),
      Concourse R.alloy R.kit R.T π Γ m N per k H ∧
      Topline (H N) (R.alloy.B.a.clock.forcedAllowance N) ∧
      ∀ i, m ≤ i → i ≤ N →
        (H i).beta = (R.family.path.rep N per i).beta ∧
        (H i).eval = (R.family.path.rep N per i).eval ∧
        Nonempty (Burn.Seed (H i) (M0 k 0 (R.alloy.B.a.budget i) (π i) (R.family.path.rep N per i).beta)) := by
  let pass : TicketP R.alloy R.kit r Q := ⟨funded,bought.1.1⟩
  obtain ⟨H,history,top⟩ := terrace r Q R.alloy R.kit simple rank R.T
    R.tuning.receipts pass π Γ path bought.1.2 bought.2 live per
  refine ⟨H,history,top,?_⟩
  intro i early late
  have registered := history.1.walk i early late
  exact ⟨registered.beta,registered.view,⟨registered.stamp.choose⟩⟩

/-- Pick the whole Wilson layout and correction family before choosing any
period, then obtain physical representatives in every one of those periods. -/
theorem original (simple : G.Simple) (bought : WilsonMovingMentorWarm.Conditions R.kit)
    {r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    {Q : r.Tab R.rolls} (funded : Pass r Q R.alloy R.kit) {k m N : ℕ}
    (rank : Burn.horizon k + 2 ≤ R.alloy.B.a.clock.J m) (live : m ≤ N) :
    ∃ π Γ, PlanV.Path r R.alloy Q (Burn.horizon k) N m π Γ ∧ ∀ per:ℕ,
      ∃ H : (i : ℕ) → RG.Rep G (R.alloy.B.a.S.side i per),
        Concourse R.alloy R.kit R.T π Γ m N per k H ∧
      Topline (H N) (R.alloy.B.a.clock.forcedAllowance N) ∧
        ∀ i, m ≤ i → i ≤ N →
          (H i).beta = (R.family.path.rep N per i).beta ∧
          (H i).eval = (R.family.path.rep N per i).eval ∧
          Nonempty (Burn.Seed (H i) (M0 k 0 (R.alloy.B.a.budget i) (π i) (R.family.path.rep N per i).beta)) := by
  obtain ⟨π,Γ,path⟩ := PlanV.began r R.alloy R.kit Q funded.formal N m live rank
  exact ⟨π,Γ,path,fun per => realized R simple bought funded rank live π Γ path per⟩

end YM.Integration.WilsonMovingMentorTerrace
end
