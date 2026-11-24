import YM.Integration.WilsonMovingMentorConcourse
import YM.Integration.WilsonMovingMentorMarkedRate

/-! A measured bound for the part of the actual regular activities outside
the marked seed, together with the original paid transition on the very same
physical representatives. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorConcourseRows
open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Org Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset
open scoped Classical Topology

variable {G : Gauge} (R : Run G)

theorem original (simple : G.Simple) (q k : ℕ) (rank : q ≤ 3*k+2) {ε : ℝ} (positive : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (N per : ℕ) (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
      (H : (i : ℕ) → Rep G (R.alloy.B.a.S.side i per)), Concourse R.alloy R.kit R.T π Γ m N per k H →
      ∀ i, m ≤ i → i ≤ N →
        ∃ C : Burn.Seed (H i) (M0 k 0 (R.alloy.B.a.budget i) (π i) (R.family.path.rep N per i).beta),
          Burn.Candor (R.alloy.B.a.budget i) (H i).activities (Set.range C.model)
            (Burn.silver (R.alloy.B.a.clock.hatBeta i)) (ε * (Pert.Asymptotics.regulatorRun R.family N per i)^q) := by
  have agree : Burn.credit k = WilsonMovingMentorMarkedRate.exponent k := by
    norm_num [Burn.credit,Burn.alt,Burn.extraN,WilsonMovingMentorMarkedRate.exponent]
    ring
  filter_upwards [WilsonMovingMentorMarkedRate.original R simple q k rank positive] with m bill N per π Γ H course i early late
  obtain ⟨C,paid⟩ := (course.1.walk i early late).stamp
  have price : Burn.young (R.alloy.B.a.clock.hatBeta i) k ≤ ε * (Pert.Asymptotics.regulatorRun R.family N per i)^q := by
    simpa only [Burn.young,agree] using bill N per i early late
  refine ⟨C,⟨?_,paid.town⟩⟩
  obtain ⟨v,regular,total⟩ := paid.sale
  refine ⟨v,regular,?_⟩
  intro o
  obtain ⟨inside,outside⟩ := total o
  exact ⟨inside,outside.1,outside.2.1,outside.2.2.trans price⟩

theorem guide {m N per k : ℕ} {π : ℕ → Layout G} {Γ : ℕ → Pace.Coin}
    {H : (i : ℕ) → Rep G (R.alloy.B.a.S.side i per)} (course : Concourse R.alloy R.kit R.T π Γ m N per k H)
    (i : ℕ) (early : m ≤ i) (late : i < N) :
    ∃ K : Opera.Guide R.alloy.B R.kit.shape N i per (H (i+1)),
      Opera.Price R.alloy.B R.kit.shape N i per (H (i+1)) K ∧
      Nonempty (QuadraticLocal.Travel.Walk K (H i) ((Time.forecastK R.alloy.B.a i R.kit.scout (H (i+1)).beta)/8)
        (Time.forecastK R.alloy.B.a i R.kit.scout (H (i+1)).beta)
        (Time.quoteHard R.alloy.B.a i R.kit.book (H (i+1)).beta) (QuadraticLocal.Willow.haloSlack (R.alloy.B.a.budget i).B)) :=
  (course.2 i early late).earns

end YM.Integration.WilsonMovingMentorConcourseRows
end
