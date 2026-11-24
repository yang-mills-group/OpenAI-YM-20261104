import YM.QuadraticLocal.Campaign.Enroll
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
namespace YM.Integration.WilsonOriginalProjectedCurvatureCourseNotice
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
local notation "u" => (R.alloy.B.a.S.oneStep m per).exact_size
local notation "intake" => (WilsonMovingMentorIncomingSlots.original R course start before)
local notation "Yh" => ((intake).2.2.choose)
local notation "Bp" => (R.alloy.B.a.budget m)
local notation "p0" => (R.kit.target (J (m+1)) (J m))
local notation "hp" => (Mentor.Cruise.walletB (m:=m) (U:=H (m+1)) root R.rolls table R.alloy R.kit ψ pass op epoch M order voter (atFine).truep.point)
local notation "shade" => (Mentor.Cruise.curtainH (m:=m) (U:=H (m+1)) root R.rolls table R.alloy R.kit ψ pass op epoch M order voter (atFine).truep.point)
local notation "published" => (Mentor.Cruise.publish root R.rolls table R.alloy ψ books op epoch u M order voter card)
local notation "bank" => (Mentor.Cruise.model root R.rolls table R.alloy ψ books op epoch u M order voter card (H (m+1)).p.B shade)
local notation "t" => (R.alloy.B.a.clock.hatBeta m)
local notation "tx" => (Pressure.betaF G t (R.rolls.L (J (m+1))))

include voter
def Clause (deposited:Burn.Seed (H (m+1))
    (WheelP.M0 epoch.vac 0 (R.alloy.B.a.budget (m+1)) card.extra (H (m+1)).beta)) : Prop :=
    Tint.Campus.Hearth.Week.Notice (U:=H (m+1)) (e:=t) (R':=H m) M input w positive (intake).1 sealed y Yh
      (Mentor.Radii.survey (p0).halo op.count op.stage (Bp).B)
      (Mentor.Radii.window (p0).halo op.count op.stage (Bp).B) deposited hp published bank
      (tx^Mentor.Tuition.need order (Mentor.Tolerance (J m)))
      (2*Trio.base (Mentor.Radii.occupancy (p0).halo op.count op.stage) (Pressure.radiusB t))


include simple education journey
theorem original (deposited:Burn.Seed (H (m+1))
    (WheelP.M0 epoch.vac 0 (R.alloy.B.a.budget (m+1)) card.extra (H (m+1)).beta)) :
    Clause R root table ψ books pass op epoch card course start before M w positive voter input sealed y deposited := by
  unfold Clause
  have band:(H (m+1)).beta ∈ Shoot.band R.alloy.B.a (m+1) := by
    rw [(atFine).beta]
    exact (R.makes.wilson.represents N per (m+1) before).band
  exact Mentor.Cruise.books (N:=N) (m:=m) root R.rolls table R.alloy R.kit ψ books pass education
    op epoch u M w order voter card journey (atFine).truep.point
    ((atFine).truep.path.trans (congr_fun (congr_fun R.alloy.B.bases N) (m+1))) input positive
    (intake).1 y sealed Yh deposited band before simple (n:=per) rfl (R':=H m) (atCoarse).truep.point

end YM.Integration.WilsonOriginalProjectedCurvatureCourseNotice
