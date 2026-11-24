import YM.Integration.WilsonMovingMentorMarkedRate
import YM.AllOrder.Transit.Summit

/-! Coupling-order regular income for the very seed used to enter the physical step. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorIssuedSeed
open Filter Lattice RG Wilson Pressure PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder AllOrder.Floe AllOrder.Transit AllOrder.Transit.WheelP ConnectedActivityE6
open scoped Topology Classical

theorem original {G : Gauge} (R : Run G) (simple : G.Simple) (q k : ℕ) (rank : q ≤ 3*k+2)
    {ε : ℝ} (positive : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (N per i : ℕ), m ≤ i → i ≤ N →
      ∀ (U : RG.Rep G (R.family.side i per)) (π : Layout G)
        (Z : Burn.Seed U (M0 k 0 (R.alloy.B.a.budget i) π U.beta)),
        U.beta=(R.family.path.rep N per i).beta →
        Burn.Candor (R.alloy.B.a.budget i) U.activities (Set.range Z.model)
          (Burn.silver (R.alloy.B.a.clock.hatBeta i)) (Burn.young (R.alloy.B.a.clock.hatBeta i) k) →
        Burn.Candor (R.alloy.B.a.budget i) U.activities (Set.range Z.model)
          (Burn.silver (R.alloy.B.a.clock.hatBeta i)) (ε*(Coat.gStep U.beta)^q) := by
  have agree : Burn.credit k = WilsonMovingMentorMarkedRate.exponent k := by
    norm_num [Burn.credit,Burn.alt,Burn.extraN,WilsonMovingMentorMarkedRate.exponent]
    ring
  filter_upwards [WilsonMovingMentorMarkedRate.original R simple q k rank positive]
    with m covers N per i early late U π Z temperature raw
  have price : Burn.young (R.alloy.B.a.clock.hatBeta i) k ≤ ε*(Coat.gStep U.beta)^q := by
    rw [temperature]
    simpa only [Burn.young,agree,Coat.gStep,Pert.Asymptotics.regulatorRun] using covers N per i early late
  refine ⟨?_,raw.town⟩
  obtain ⟨v,regular,total⟩ := raw.sale
  refine ⟨v,regular,?_⟩
  intro o
  obtain ⟨inside,outside⟩ := total o
  exact ⟨inside,outside.1,outside.2.1,outside.2.2.trans price⟩

end YM.Integration.WilsonMovingMentorIssuedSeed
end
