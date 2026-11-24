import YM.Integration.WilsonMovingMentorDatedCourse
import YM.Integration.WilsonMovingMentorItinerary
import YM.Integration.WilsonMovingMentorIssuedSeed

/-! On the original marked history, each entering seed uses its nominated card and actual coupling. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorTerraceCard
open Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Org Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit AllOrder.Transit.WheelP
open Filter MeasureTheory AnalyticBridge VerifiedReset WilsonMovingMentorItinerary ConnectedActivityE6
open scoped Topology Classical

theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
    (bought : WilsonMovingMentorWarm.Conditions R.kit)
    {r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    {Q : r.Tab R.rolls} (funded : Pass r Q R.alloy R.kit)
    (q k : ℕ) (grade : q ≤ 3*k+2) {ε : ℝ} (positive : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, m ≤ N →
      ∃ (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
        (cards : (t : Set.Ico m N) → CardAt R r k t)
        (price : ∀ t : Set.Ico m N, Burn.horizon k+2 ≤ R.alloy.B.a.clock.J t),
        PlanV.Path r R.alloy Q (Burn.horizon k) N m π Γ ∧
        (∀ t : Set.Ico m N, let C := cards t
          PlanV.Journey r R.alloy (m:=t) (N:=N) C ∧ π (t+1)=C.extra ∧
          π t=(PlanV.litP r R.alloy Q (price t) C).laid C ∧
          Γ t=(PlanV.litP r R.alloy Q (price t) C).issue C ∧
          ∀ z ∈ Age.scope (Burn.horizon k+2), z.r=2 →
            |Γ t z.e| ≤ PlanV.capprice R.alloy (Burn.horizon k) t z) ∧
        ∀ per, ∃ H : (t : ℕ) → RG.Rep G (R.alloy.B.a.S.side t per),
          Concourse R.alloy R.kit R.T π Γ m N per k H ∧
          Topline (H N) (R.alloy.B.a.clock.forcedAllowance N) ∧
          ∀ t : Set.Ico m N,
            RG.Shoot.Lives R.alloy.B.bake N t per (H t) ∧
            RG.Shoot.Lives R.alloy.B.bake N (t+1) per (H (t+1)) ∧
            (H t).beta = (R.family.path.rep N per t).beta ∧
            (H t).eval = (R.family.path.rep N per t).eval ∧
            (H (t+1)).eval = (R.family.path.rep N per (t+1)).eval ∧
            (H (t+1)).beta = (R.family.path.rep N per (t+1)).beta ∧
            (H (t+1)).beta ∈ RG.Shoot.band R.alloy.B.a (t+1) ∧
            ∃ Z : Burn.Seed (H (t+1))
                (M0 k 0 (R.alloy.B.a.budget (t+1)) (cards t).extra (H (t+1)).beta),
              Burn.Candor (R.alloy.B.a.budget (t+1)) (H (t+1)).activities (Set.range Z.model)
                (Burn.silver (R.alloy.B.a.clock.hatBeta (t+1)))
                (Burn.young (R.alloy.B.a.clock.hatBeta (t+1)) k) ∧
              Burn.Candor (R.alloy.B.a.budget (t+1)) (H (t+1)).activities (Set.range Z.model)
                (Burn.silver (R.alloy.B.a.clock.hatBeta (t+1))) (ε*(Coat.gStep (H (t+1)).beta)^q) ∧
              ∃ K : Opera.Guide R.alloy.B R.kit.shape N t per (H (t+1)),
                Opera.Price R.alloy.B R.kit.shape N t per (H (t+1)) K ∧
                Nonempty (QuadraticLocal.Travel.Walk K (H t)
                  ((Time.forecastK R.alloy.B.a t R.kit.scout (H (t+1)).beta)/8)
                  (Time.forecastK R.alloy.B.a t R.kit.scout (H (t+1)).beta)
                  (Time.quoteHard R.alloy.B.a t R.kit.book (H (t+1)).beta)
                  (QuadraticLocal.Willow.haloSlack (R.alloy.B.a.budget t).B)) := by
  filter_upwards [WilsonMovingMentorDatedCourse.original R simple bought funded q k grade positive,
    WilsonMovingMentorIssuedSeed.original R simple q k grade positive] with m atDate salary N live
  obtain ⟨π,Γ,path,available⟩ := atDate N live
  obtain ⟨cards,price,route⟩ := WilsonMovingMentorItinerary.original R funded.formal path
  refine ⟨π,Γ,cards,price,path,route,?_⟩
  intro per
  obtain ⟨H,history,hard,_⟩ := available per
  refine ⟨H,history,hard,?_⟩
  intro t
  have after := Nat.le_trans t.property.1 (Nat.le_succ t.val)
  have here := history.1.walk t t.property.1 t.property.2.le
  have there := history.1.walk (t+1) after (Nat.succ_le_of_lt t.property.2)
  refine ⟨here.truep,there.truep,here.beta,here.view,there.view,there.beta,?_,?_⟩
  · rw [there.beta]
    exact (R.makes.wilson.represents N per (t+1) (Nat.succ_le_of_lt t.property.2)).band
  have anchored := there.stamp
  rw [← there.beta,(route t).2.1] at anchored
  obtain ⟨Z,raw⟩ := anchored
  exact ⟨Z,raw,salary N per (t+1) after (Nat.succ_le_of_lt t.property.2)
    (H (t+1)) (cards t).extra Z there.beta raw,(history.2 t t.property.1 t.property.2).earns⟩

end YM.Integration.WilsonMovingMentorTerraceCard
end
