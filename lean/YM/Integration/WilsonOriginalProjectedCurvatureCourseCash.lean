import YM.QuadraticLocal.Union.Law
import YM.Integration.WilsonOriginalProjectedCurvatureReceivedSeal
import YM.Integration.WilsonMovingMentorIncomingSlots
import YM.Integration.WilsonMovingMentorTerraceCard
import YM.Integration.WilsonOriginalProjectedCurvatureOnCard

/-! The measured lower-chart comparison on the very same original upper card,
submitted signed input, physical history, certified field and paid compartment. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureCourseCash
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
local notation "atCoarse" => (course.1.walk m start before.le)
local notation "ratio" => (R.alloy.B.a.S.oneStep m per).exact_size
local notation "intake" => (WilsonMovingMentorIncomingSlots.original R course start before)
local notation "guide" => ((intake).2.2.choose)

open ConnectedActivityE6
variable (forecast:Mentor.Forecast root R.rolls table ψ books)
  (hospital:QuadraticLocal.MintClock.Hospital root R.rolls table R.kit.target ψ books forecast R.alloy.delay)
  (κ:ℕ)
local notation "paid" => (Mentor.Cruise.Semester.figure root R.rolls table R.alloy R.kit ψ books op epoch order forecast κ)
local notation "bill" => (Mentor.Cruise.Semester.expense root R.rolls table R.alloy R.kit ψ books op epoch order forecast κ)

include course start before voter hospital pass in
/-- The dated tuition is bought on the represented earlier field, its actual upper chart and both budgets. -/
theorem original (height:op.count ≤ Burn.horizon epoch.vac+2) (width:κ ≤ R.alloy.B.a.clock.J m):
    bill ≤ QuadraticLocal.MintClock.Page.reward (R.alloy.B.a.clock.hatBeta (m+1))
      (Beaming.grain (R.alloy.B.a.clock.J m)) ∧
    (paid).Cashier G (Pane.panel R.alloy m ratio).ratio.count (H (m+1)).p (H m).p bill
      (Willow.haloSlack (R.alloy.B.a.budget m).B) (Coat.gStep (H (m+1)).beta) ∧
    (paid).before = Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (R.alloy.B.a.clock.J (m+1)) ∧
    (paid).count=op.count ∧ (paid).cause=order ∧ (paid).rank=κ ∧ (paid).stage=op.stage:= by
  have band:(H (m+1)).beta ∈ Shoot.band R.alloy.B.a (m+1):=by
    rw [(atFine).beta]
    exact (R.makes.wilson.represents N per (m+1) before).band
  obtain ⟨earned,cash⟩:=Mentor.Cruise.Semester.tight (M:=M) (Vv:=voter) (h:=pass) (u:=ratio)
    (hF:=(atFine).truep.point) (hk:=(atCoarse).truep.point) (Qa:=forecast) (hc:=hospital)
    (hβ':=band) (Yh:=guide) (hs:=height) (hκr:=width)
  exact ⟨earned,cash,rfl,rfl,rfl,rfl,rfl⟩

end YM.Integration.WilsonOriginalProjectedCurvatureCourseCash
