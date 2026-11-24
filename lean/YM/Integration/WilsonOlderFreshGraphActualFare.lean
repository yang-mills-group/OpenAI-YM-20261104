import YM.Integration.WilsonOlderFreshGraphCommonSalary
import YM.Integration.WilsonMeasuredSemesterSubpower

/-! The expense in the source amplitude is the actual measured-age
semester expense of this offered field. Its original forecast covers
every numerical test before either regulator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphActualFare
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G){m i N per k Q d:ℕ}
  (hk:Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q₀:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q₀ φ)
  (chamber:VowsR.Chamber scroll R.kit D Q₀ books) (hi:m ≤ i)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
  (school:Syl.School k)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q₀ π Γ hi)
  (cal:Oak.Calendar R hk D Q₀ π Γ Ψ hi (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q₀ φ books)
  (hospital:MintClock.Hospital D R.rolls Q₀ R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀"=> Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
variable (y:Site (R.family.side (i+1) per))
local notation "S"=>WilsonOlderFreshGraphPointWallet.point y
local notation "letterPost"=>Earn.Passport.point (fun _:Unit=>y)

variable (A:Unit→Set ℂ)
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter

variable {dmax:ℕ} (L:Primer.Families R.family) (a:hue G) (depth:d<dmax)
    (w:Letter (R.family.labels.level d)) (f:Studio dmax)
local notation "Ω₀"=>Oak.expenseReal R hk D Q₀ π Γ books hi op lesson ahead school.order school.horizon

include history hospital y in
theorem original (T:WilsonOlderFreshGraphSlate.Copy G d Q σ₀) (nonbare:i<N) (cap:∀t,‖value A t‖ ≤ 1)
    (seats:1 ≤ op.count) (shape:op.count=school.pieces) (phase:school.order+1 ≤ op.stage)
    (enrolled:Q ≤ school.order) (order:d ≤ school.horizon) (budget:school.order+d ≤ Burn.horizon k+2)
    (pass:Pass D Q₀ R.alloy R.kit) (δ:ℝ) (pos:0<δ) (live:WilsonMeasuredSemesterSubpower.onset R 1 pos ≤ i):
    0 < Ω₀ ∧ Ω₀ ≤ (R.alloy.B.a.clock.hatBeta (i+1))^δ :=by
  have right:=hk.trans (R.alloy.B.a.fits.mono hi)
  have reserve:school.horizon ≤ R.alloy.B.a.clock.J i:=
    (Nat.le_add_left school.horizon school.order).trans (school.tall.trans right)
  have qo:Q ≤ R.alloy.B.a.clock.J i:=enrolled.trans
    ((Nat.le_add_right school.order school.horizon).trans (school.tall.trans right))
  have vote:Cruise.Voter (T.rows S A) σ₀ school.order op.count op.stage k (R.alloy.B.a.clock.J i):=
    T.voted S A cap (ord:=school.order) (seats:=op.count) (stage:=op.stage) (vac:=k) (shelf:=R.alloy.B.a.clock.J i)
      seats phase budget qo (order.trans reserve)
  let iw:=history.1.walk i hi nonbare.le
  let jw:=history.1.walk (i+1) (Nat.le_succ_of_le hi) nonbare
  let pay:=(WilsonMovingMentorIncomingSlots.original R history hi nonbare).2.2.choose
  have band:(Ψ (i+1)).beta∈Shoot.band R.alloy.B.a (i+1):=jw.beta ▸
    (R.makes.wilson.represents N per (i+1) nonbare).band
  have receipt:=Mentor.Cruise.Semester.tight D R.rolls Q₀ R.alloy R.kit φ books pass op
    (Oak.era R hk D Q₀ π Γ hi op lesson) (R.alloy.B.a.S.oneStep i per).exact_size (T.rows S A)
    school.order vote ahead jw.truep.point pay iw.truep.point hospital (shape.trans_le school.sense)
    school.horizon reserve band
  have Ωpos:0<Ω₀:=receipt.2.paysAbove
  have Ωbill:Ω₀ ≤ (R.alloy.B.a.clock.hatBeta (i+1))^Beaming.grain (R.alloy.B.a.clock.J i):=
    receipt.1.trans (min_le_right ..)
  have all:=(eventually_atTop.mp (WilsonMeasuredSemesterSubpower.budget R 1 pos)).choose_spec i live Ω₀ Ωpos.le Ωbill
  exact ⟨Ωpos,by simpa using all⟩
end YM.Integration.WilsonOlderFreshGraphActualFare
end
