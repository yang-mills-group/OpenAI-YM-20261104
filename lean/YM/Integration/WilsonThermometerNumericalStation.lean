import YM.Integration.WilsonThermometerNumericalBank
import YM.Integration.WilsonOriginalCoveredEvolution

/-! Both independent dates for the literal registered thermometer evaluated
on a separately constructed bank of raw words and frozen fitted numbers.
Every field restriction uses the same bank, quiet layout and back series. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerNumericalStation
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonOriginalThermometerTopDensity FVA1Physical.TwoReset Stationary
open Further.PhysicalPeriodLimitF933
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m per k i:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m (i+1) per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (chamber:VowsR.Chamber scroll R.kit D Q books) (hi:m ≤ i)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ (i+1)) (R.family.path.levels.clock.forcedAllowance (i+1)))
  (school:Syl.School k) (w:Fin 3→ℝ)
  (o:Positions (Fin 3) (R.family.side (i+1) per))
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=i+1) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=i+1) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "M₀" => primitive R A (i+1) per o.origin σ₀
local notation "S₀" => WilsonThermometerCourseHearing.sectors
local notation "P₀" => Ψ (i+1)
local notation "J₀" => Stock.census (Fin 3)
local notation "E₀" => Passport.point o.origin
local notation "Ω₀" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead school.order school.horizon
local notation "head" => WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self i) o

local notation "tape₀" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "teach" P:max => Oak.student (n:=per) R hk D Q π Γ books hi (P).op (P).lesson ahead disks
  (P).model school.order (P).voter


local notation "g₂" => Pert.Asymptotics.regulatorRun R.family (i+1) per (i+1)
local notation "τ₂" => (R.family.path.rep (i+1) per (i+1)).p.threshold
local notation "v₂" => WilsonOriginalThermometerPalette.coordinates R A (i+1) (i+1) per
local notation "report" => R.family.side i per

def numerical (x : Wallet disks) : WilsonOriginalCopiedHistory.Values G (J₀) (report) :=
  WilsonOriginalCopiedHistory.block R (Nat.lt_succ_self i) school.order (fun _ mult =>
    WilsonThermometerNumericalBank.bank R levels o.origin (g₂) (τ₂) (v₂) probe mult x (π (i+1)) tape₀)

theorem original (x : Wallet disks) :
    WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o x =
      numerical R A π school o x := by
  unfold WilsonThermometerRegisteredPupil.bare numerical
  apply congrArg (WilsonOriginalCopiedHistory.block R (Nat.lt_succ_self i) school.order)
  funext grid mult
  exact WilsonThermometerNumericalBank.same R levels o.origin (σ₀) (g₂) (τ₂) (v₂) probe
    WilsonOriginalThermometerGradedPalette.positive mult x (π (i+1)) tape₀

/-- Substitution occurs before the lower finite contraction, retaining the
entire deposited face program and the clock used by both quiet and marked rows. -/
theorem returned (x : Wallet disks) :
    WilsonOriginalCoveredEvolution.run R (Nat.lt_succ_self i) π Γ (Burn.horizon k+2) school.order levels
      (WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o x) =
    WilsonOriginalCoveredEvolution.run R (Nat.lt_succ_self i) π Γ (Burn.horizon k+2) school.order levels
      (numerical R A π school o x) := by
  rw [original]

end YM.Integration.WilsonThermometerNumericalStation
