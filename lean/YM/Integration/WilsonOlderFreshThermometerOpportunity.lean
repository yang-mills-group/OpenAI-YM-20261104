import YM.Integration.WilsonThermometerThreeCompactHard
import YM.Integration.WilsonOlderFreshGraphActualFare

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace YM.Integration.WilsonOlderFreshThermometerOpportunity
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open WilsonOriginalPointCompactRoster WilsonOriginalPointCompactCash WilsonOriginalThreeCompactProduct
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m i N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ} (scroll:LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (hi:m ≤ i) (cut:i < N)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (chamber:VowsR.Chamber scroll R.kit D Q books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)

local notation "H" => Ψ (i+1)
local notation "g" => Coat.gStep (H).beta
variable {I:Type} [Fintype I] {q:ℕ} (owner:I→Fin 3) (grades:Fin 3→ℕ)
  (sites:Fin 3→Site (R.family.side (i+1) per))
  (T:(z:I)→WilsonOlderFreshGraphSlate.Copy G (grades (owner z)) q (Poetry.Agenda.seed (G:=G) (U:=R.metals.K) (F:=R.metals.p.profile) (K:=R.metals.p.kernel) D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))))
  (A:Fin 3→Set ℂ) (charge:I→ℂ) (order shelf:ℕ)
local notation "M" => rows owner grades sites T A charge
local notation "J" => Stock.census (Fin 3)
local notation "S₀" => (fun _:Fin 3=>(⊥:Submodule ℝ ℂ))
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead order shelf
local notation "wage" => WilsonOriginalPointCompactSalary.invoice owner grades sites T charge
local notation "physical" => (fun t U=>((H).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut M (g) t U))

attribute [local irreducible] Poetry.Agenda.seed


include course cut chamber hospital I owner sites T charge in
theorem original (qorder:q ≤ order)(slots:3 ≤ op.count)(count:op.count ≤ Burn.horizon k+2)
    (fit:(∑v:Fin 3,grades v) ≤ shelf)(level:shelf ≤ R.alloy.B.a.clock.J i)
    (stage:order+1 ≤ op.stage)(size:order+(∑v:Fin 3,grades v) ≤ Burn.horizon k+2)
    (unit:∀v(t:ℂ),t∈A v → ‖t‖ ≤ 1){δ:ℝ}(pos:0<δ)
    (live:WilsonMeasuredSemesterSubpower.onset R 1 pos ≤ i):
    0<Ω ∧ Ω ≤ (R.alloy.B.a.clock.hatBeta (i+1))^δ :=by
  have past:= hk.trans (R.alloy.B.a.fits.mono hi)
  have qfits:q ≤ R.alloy.B.a.clock.J i:=qorder.trans ((Nat.le_add_right _ _).trans (size.trans past))
  let σ:=Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
  have σ0:0 ≤ σ:=(Poetry.Agenda.stem D φ _ _).le
  have vote:=@WilsonOriginalPointCompactVoter.original G (R.family.side (i+1) per) I inferInstance q σ
    owner grades sites T A charge σ0 unit order op.count op.stage k (R.alloy.B.a.clock.J i)
    slots (fit.trans level) qorder qfits stage size
  let iw:=course.1.walk i hi cut.le
  let jw:=course.1.walk (i+1) (Nat.le_succ_of_le hi) cut
  let pay:=(WilsonMovingMentorIncomingSlots.original R course hi cut).2.2.choose
  have band:(Ψ (i+1)).beta∈Shoot.band R.alloy.B.a (i+1):=jw.beta ▸
    (R.makes.wilson.represents N per (i+1) cut).band
  have receipt:=Mentor.Cruise.Semester.tight D R.rolls Q R.alloy R.kit φ books chamber.station.pledge op
    (Oak.era R hk D Q π Γ hi op lesson) (R.alloy.B.a.S.oneStep i per).exact_size M
    order vote ahead jw.truep.point pay iw.truep.point hospital count shelf level band
  have positive:0<Ω:=receipt.2.paysAbove
  have invoice:Ω ≤ (R.alloy.B.a.clock.hatBeta (i+1))^Beaming.grain (R.alloy.B.a.clock.J i):=
    receipt.1.trans (min_le_right ..)
  have resource:=(Filter.eventually_atTop.mp (WilsonMeasuredSemesterSubpower.budget R 1 pos)).choose_spec i live Ω positive.le invoice
  exact ⟨positive,by simpa using resource⟩

end YM.Integration.WilsonOlderFreshThermometerOpportunity
end
