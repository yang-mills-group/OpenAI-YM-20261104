import YM.Integration.WilsonOriginalProjectedCurvatureAdmittedStep
import YM.Integration.WilsonCoherentMayerCourseGross
import YM.Integration.WilsonOriginalProjectedCurvaturePublishedCover

/-! The true filed angular return and all of its rejected letters use one nonbare cashier. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPublishedSlip
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
  (input:Tint.Incoming D (H (m+1)) α Empty ρ) (y:α)

local notation "atFine" => (course.1.walk (m+1) (Nat.le_succ_of_le start) before)

open ConnectedActivityE6 LocalComparison
variable (forecast:Mentor.Forecast root R.rolls table ψ books)
  (hospital:QuadraticLocal.MintClock.Hospital root R.rolls table R.kit.target ψ books forecast R.alloy.delay)
  (vol:ℕ)
local notation "earnings" => (Mentor.Cruise.Semester.figure root R.rolls table R.alloy R.kit ψ books op epoch order forecast vol)
local notation "fee" => (Mentor.Cruise.Semester.expense root R.rolls table R.alloy R.kit ψ books op epoch order forecast vol)


local notation "siteSize" => (R.alloy.B.a.S.oneStep m per).exact_size
local notation "published" => (Mentor.Cruise.publish root R.rolls table R.alloy ψ books op epoch siteSize M order voter card)
local notation "actualReceipt" => (Mentor.Cruise.funded root R.rolls table R.alloy ψ books op epoch siteSize M order voter card journey forecast)

include simple education journey upper hospital
theorem original (tolls:V→ℕ) (q j k v:ℕ)
    (height:op.count ≤ Burn.horizon epoch.vac+2) (room:vol ≤ R.alloy.B.a.clock.J m)
    (rows:Scene.Armada M w tolls (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (R.alloy.B.a.clock.J (m+1)))
      fee⁻¹ j k v) (jet:j ≤ order) (crew:k ≤ op.count) (placed:v ≤ vol)
    (retained:input.hard.Paid w (H (m+1)).p.B (H (m+1)).p.supportExponent
      (((R.alloy.B.a.clock.hatBeta (m+1))^(-(q:ℝ)))*forcedDivisor R.family (m+1))):
    WilsonRootedKioskOccupiedSlip.Gross (Width.treasured M (Pane.panel R.alloy m siteSize).ratio
      published actualReceipt (H m).p (earnings).afterwards (Coat.gStep (H (m+1)).beta)) w (H m).p.B
      ((H m).p.supportExponent+1) (((Spill.allOver (H m).p)^(earnings).cap)*fee) ∧
    ∃ sealed:Travel.Seal (Tint.Patrol.picture M input) w 2 1,
      Tint.Campus.Investor.Medal M input w sealed 0 ((Coat.gStep (H (m+1)).beta)^op.stage) ∧
    ∃ Z : Burn.Seed (H (m+1))
      (WheelP.M0 epoch.vac 0 (R.alloy.B.a.budget (m+1)) card.extra (H (m+1)).beta),
      Burn.Candor (R.alloy.B.a.budget (m+1)) (H (m+1)).activities (Set.range Z.model)
        (Burn.silver (R.alloy.B.a.clock.hatBeta (m+1)))
        (Burn.young (R.alloy.B.a.clock.hatBeta (m+1)) epoch.vac) ∧
      WilsonOriginalProjectedCurvatureCourseNotice.Clause R root table ψ books pass op epoch card course start before M w positive voter input sealed y Z := by
  have booked:=WilsonOriginalProjectedCurvatureCourseCash.original
    (R:=R) (root:=root) (table:=table) (ψ:=ψ) (books:=books) (pass:=pass) (op:=op)
    (epoch:=epoch) (course:=course) (start:=start) (before:=before) (order:=order) (M:=M) (voter:=voter)
    (forecast:=forecast) (hospital:=hospital) (κ:=vol) (height:=height) (width:=room)
  constructor
  · exact WilsonCoherentMayerCourseGross.original M w tolls (Pane.panel R.alloy m siteSize).ratio
      earnings published actualReceipt booked.2.1 rows jet crew placed (by linarith)
  · exact WilsonOriginalProjectedCurvatureAdmittedStep.original R simple root table ψ books pass education
      op epoch card journey upper course start before M w positive voter input y forecast hospital vol
      tolls q j k v height room rows jet crew placed retained

end YM.Integration.WilsonCoherentMayerPublishedSlip
