import YM.Integration.WilsonMovingMentorConcourse

/-! The original Chartlet and the continuing charged walk use exactly the same physical guide on each enrolled torus. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorChartlet
open Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Org Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit AllOrder.Transit.WheelP
open scoped Classical

variable {G : Gauge} (R : Run G)


open PhysicalNext.Repeat.Boulevard
theorem original {π : ℕ → Layout G} {Γ : ℕ → Pace.Coin} {k m N per : ℕ}
    {H : (i : ℕ) → RG.Rep G (R.alloy.B.a.S.side i per)}
    (course : Concourse R.alloy R.kit R.T π Γ m N per k H)
    {i : ℕ} (early : m ≤ i) (old : i < N) :
    let a := R.alloy.B.a
    let ratio := (a.S.oneStep i per).exact_size
    ∃ K : Chartlet R.kit.shape R.alloy N i ratio (H (i+1)),
      SeekR R.kit.shape R.alloy N i ratio K ∧
      Nonempty (QuadraticLocal.Travel.Walk K (H i)
        ((AnalyticBridge.VerifiedReset.Time.forecastK a i R.kit.scout (H (i+1)).beta)/8)
        (AnalyticBridge.VerifiedReset.Time.forecastK a i R.kit.scout (H (i+1)).beta)
        (AnalyticBridge.VerifiedReset.Time.quoteHard a i R.kit.book (H (i+1)).beta) (QuadraticLocal.Willow.haloSlack (a.budget i).B)) :=
  (course.2 i early old).earns

end YM.Integration.WilsonMovingMentorChartlet
end
