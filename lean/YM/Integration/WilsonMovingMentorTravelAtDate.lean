import YM.Integration.WilsonMovingMentorTravel
import YM.Integration.WilsonMovingMentorMarkedRate

/-! The original Transit reader at the measured upper Wilson temperature. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorTravelAtDate
open RG Push Push.PriceCompiler PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Org AllOrder AllOrder.Floe.Step AllOrder.Transit Next.Foundations
open Progress.DirectedRecipe
open Pressure Precision RG.Supply PhysicalNext.ThroughLaunch PhysicalNext.Repeat.Roof

variable {G : Gauge} (R : Run G)
variable {r : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
variable {Q : r.Tab R.rolls} (funded : Pass r Q R.alloy R.kit)
include funded

/-- A single original Tour covers all measured adjacent stages. -/
theorem at_date (m : ℕ) :
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    Noon R.kit.shape r Q R.kit.v R.kit.prices R.kit.t R.kit.span
      R.kit.recordP R.kit.scout (wind R.kit.menu) j i (R.alloy.B.a.clock.hatBeta m) :=
  funded.tour.actors _ _ _ (R.alloy.B.valid.pays m) (step_paid R.alloy.B.a m)

/-- The original rate uses the represented field temperature at the fine date. -/
theorem measured {m N : ℕ} (live : m<N) (per : ℕ) :
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    let x := R.alloy.B.a.clock.hatBeta m
    let y := R.alloy.B.a.clock.hatBeta (m+1)
    let β := (R.family.path.rep N per (m+1)).beta
    let b := R.kit.book j i
    Payments.Rates (radiusB x) (Real.exp (-Payments.Pairing.kGoal b y β))
      ((R.kit.scout j i).pair.strong y β) (x^(-(1/3:ℝ))) (Payments.Pairing.kGoal b y β) := by
  dsimp only
  rw [beta_eq R.alloy.B.valid m]
  apply (at_date R funded m).pays
  rw [← beta_eq R.alloy.B.valid m]
  obtain ⟨lo,hi⟩ := (R.makes.wilson.represents N per (m+1) live).band
  change R.alloy.B.a.clock.hatBeta (m+1)/2 ≤ (R.family.path.rep N per (m+1)).beta at lo
  change (R.family.path.rep N per (m+1)).beta ≤ 2*R.alloy.B.a.clock.hatBeta (m+1) at hi
  change _/4 ≤ _ ∧ _ ≤ 4*_
  constructor <;> linarith only [lo,hi]

end YM.Integration.WilsonMovingMentorTravelAtDate
end
