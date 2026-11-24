import YM.Integration.WilsonOriginalProjectedCurvatureCourseNotice
/-! One physically issued upper seed for the same lower signed comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureIssuedNotice
open Function Finset Filter Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn
open Org Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP PhysicalNext.Repeat.Boulevard
open AnalyticBridge VerifiedReset
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple)
  {V α ι KU:Type} [DecidableEq V] [Fintype V] [Countable ι] [Countable KU]
  (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (table:root.Tab R.rolls) (ψ:ℕ→ℕ) (books:Mentor.Offices.Books root R.rolls table ψ)
  (pass:Pass root table R.alloy R.kit)
  (education:Mentor.Educated root R.rolls table R.kit.shape R.kit.scout ψ books R.alloy.delay)
  {first m N per order:ℕ} {π:ℕ→Layout G} {Γ:ℕ→Pace.Coin}
  {H:(s:ℕ)→Rep G (R.family.side s per)}
local notation "J" => R.alloy.B.a.clock.J
variable (op:Mentor.Opportunity (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m))
  (epoch:Mentor.Epoch root R.rolls (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m) op)
  (card:WilsonMovingMentorItinerary.CardAt R root epoch.vac m)
  (journey:PlanV.Journey root R.alloy (N:=N) (m:=m) card) (upper:π (m+1)=card.extra)
  (course:Concourse R.alloy R.kit R.T π Γ first N per epoch.vac H)
  (start:first ≤ m) (before:m < N)
  {D:Passport (R.family.side (m+1) per) V} {ρ:Census V}
  (M:ι→Row D ρ G α) (w:V→ℝ) (positive:∀j,0<w j)
  (voter:Mentor.Cruise.Voter M (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (R.alloy.B.a.clock.J (m+1)))
    order op.count op.stage epoch.vac (R.alloy.B.a.clock.J m))
  (input:Tint.Incoming D (H (m+1)) α KU ρ) {b b':ℝ}
  (sealed:Travel.Seal (Tint.Patrol.picture M input) w b b') (y:α)

local notation "atFine" => (course.1.walk (m+1) (Nat.le_succ_of_le start) before)
include simple education journey upper
/-- The row and the regular residual use the same issued upper seed. -/
theorem held :
    ∃ Z : Burn.Seed (H (m+1))
      (WheelP.M0 epoch.vac 0 (R.alloy.B.a.budget (m+1)) card.extra (H (m+1)).beta),
      Burn.Candor (R.alloy.B.a.budget (m+1)) (H (m+1)).activities (Set.range Z.model)
        (Burn.silver (R.alloy.B.a.clock.hatBeta (m+1)))
        (Burn.young (R.alloy.B.a.clock.hatBeta (m+1)) epoch.vac) ∧
      WilsonOriginalProjectedCurvatureCourseNotice.Clause R root table ψ books pass op epoch card course start before M w positive voter input sealed y Z := by
  have anchored := (atFine).stamp
  rw [← (atFine).beta, upper] at anchored
  obtain ⟨Z, usable⟩ := anchored
  exact ⟨Z,usable,WilsonOriginalProjectedCurvatureCourseNotice.original (R:=R) (simple:=simple) (root:=root) (table:=table) (ψ:=ψ)
    (books:=books) (pass:=pass) (education:=education) (op:=op) (epoch:=epoch) (card:=card)
    (journey:=journey) (course:=course) (start:=start) (before:=before) (M:=M) (w:=w)
    (positive:=positive) (voter:=voter) (input:=input) (sealed:=sealed) (y:=y) Z⟩

end YM.Integration.WilsonOriginalProjectedCurvatureIssuedNotice
