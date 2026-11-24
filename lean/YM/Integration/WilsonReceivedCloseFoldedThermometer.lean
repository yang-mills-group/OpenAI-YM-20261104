import YM.Integration.WilsonReceivedCloseHouseHearing
import YM.Integration.WilsonReceivedCloseFoldedOrdinary
import YM.Integration.WilsonOriginalCoveredHearing

/-! The positioned three-field source against its independently issued original folded program.
All orientations, test vectors and physical subsets use one paid trajectory. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCloseFoldedThermometer
open Pert.Asymptotics
open WilsonOriginalReceivedChain WilsonReceivedCloseHistory Extra.Histories MergeProof.Accent
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonLimitConstruction WilsonOriginalStarSceneRent WilsonOriginalThermometerMicroscopic
open WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m per k i:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m (i+2) per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (chamber:VowsR.Chamber scroll R.kit D Q books) (hi:m ≤ i+1)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ (i+2)) (R.family.path.levels.clock.forcedAllowance (i+2)))
  (school:Syl.School k)
  (o:Positions (Fin 3) (R.family.side (i+2) per))
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+2)) (R.alloy.B.a.clock.J (i+1)))
  (lesson:Lesson (N:=i+2) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=i+2) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+2))
local notation "M₀" => primitive R A (i+2) per o.origin σ₀
local notation "S₀" => WilsonThermometerCourseHearing.sectors
local notation "P₀" => Ψ (i+2)
local notation "J₀" => Stock.census (Fin 3)
local notation "E₀" => Passport.point o.origin
local notation "Ω₀" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead school.order school.horizon
local notation "head" => WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self (i+1)) o

variable {f:Extraction.Order} {F:(Bel R.family.book).Hierarchy} {δ:ℝ} {T:Campaign R}
  {W:Campaign.Pillars R T} (fund:FundedOriginalProperties.{u} simple δ W) (slow:WilsonWindowReportingPace.Slow R.kit)

open FVA1Physical.TwoReset

local notation "E₁" => max 1 ((1+WilsonOriginalThermometerReportedGrading.cap R i 1)*wallet R levels σ₀)
local notation "w₁" => (fun _:Fin 3 => ((E₁)*(Ω₀))⁻¹)


local notation "x₀" => regulatorRun R.family (i+2) per (i+1)
local notation "U₀" => WilsonReceivedCloseReportedWallet.unit R
local notation "initial" => WilsonOriginalReceivedChain.Post (N:=i+2) R hk D Q π Γ Ψ books ahead disks
  (S₀) levels school.order school.horizon school.pieces (i+1) hi (head)
local notation "sale" S:max => WilsonReceivedCloseNamedWallet.Sold (N:=i+2) (b:=i+1) (V:=Fin 3) (X:=fun _=>ℂ) R hk D Q π Γ Ψ books ahead disks (S₀) levels
  school.order school.horizon school.pieces hi (head) S univ (U₀*(x₀⁻¹)^37)
local notation "faces" S:max q:max span:max H:max ac:max ε:max => WilsonReceivedCloseOrdinaryRoster.Served (N:=i+2) (b:=i+1) (V:=Fin 3) (X:=fun _=>ℂ) R hk D Q π Γ Ψ
  books ahead disks (S₀) levels school.order school.horizon school.pieces hi (head) S (Nat.lt_succ_self (i+1))
  span H ac univ 3 (U₀*(x₀⁻¹)^37) (x₀^(q+37*3+1+3)) (ε*x₀^q)
local notation "entryprogram" x:max => WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o x
local notation "return₃" x:max => WilsonOriginalCoveredEvolution.run (N:=i+2) R (Nat.lt_succ_self (i+1))
    π Γ (Burn.horizon k+2) school.order levels (entryprogram x)

open Laurent Stationary Comparison.RG02 Order
local notation "bareReturn" => (fun (j:ℕ)(jb:j ≤ i+1)(x:Wallet disks)(field:Stationary.Link G (R.family.side j per))(lag:ℕ) =>
  (return₃ x) j jb (R.family.side j per) (dvd_refl _) lag field)
local notation "folded" S:max q:max span:max H:max cap:max eps:max =>
  WilsonReceivedCloseFoldedOrdinary.Heard R hk D Q π Γ Ψ books ahead disks (S₀) levels school.order school.horizon
    school.pieces hi (head) S (Nat.lt_succ_self (i+1)) bareReturn span H cap univ 3 37 q (U₀) eps
def Receipt (q prec span:ℕ) (H angleCap ε:ℝ) : Prop :=
    ∃ S:initial, S.w=w₁ ∧ S.rent=x₀^prec ∧ S.passport=E₀ ∧ S.inputIndex=Empty ∧
      S.op=op ∧ S.lesson=lesson ∧ WilsonReceivedCloseReportedStation.Filed R simple A hk D Q π Γ Ψ
        books hi school o ahead S ∧ WilsonReceivedCloseCopiedThermometer.Published R simple A hk D Q π Γ Ψ books hi school o ahead S ∧ sale S ∧ faces S q span H angleCap (ε/2) ∧ folded S q span H angleCap ε
variable (q prec span shape:ℕ) (height angleCap cap ε:ℝ) (hp:0≤angleCap) (ep:0<ε)
  (volume:Volume.Fund D R.rolls Q φ books R.alloy.delay) (stage:k ≤ R.alloy.B.a.clock.J m)
  (close:PaceR.Close R shape cap m (i+1))
local notation "gate" => WilsonReceivedCloseFoldedOrdinary.Ready (k:=k) R D (φ:=φ) levels school.order school.horizon
    school.pieces simple 3 37 q shape span (U₀) cap height angleCap ε (WilsonReceivedCloseReportedWallet.covers R) hp ep m

include history chamber volume stage close in
theorem original (dates:gate)
    (intake:WilsonReceivedCloseHouseHearing.Receipt R simple A hk D Q π Γ Ψ books hi school o op lesson ahead
      q prec span height angleCap (ε/2)) :
    Receipt R simple A hk D Q π Γ Ψ books hi school o op lesson ahead q prec span height angleCap ε := by
  rcases intake with ⟨S,aperture,loss,passport,bare,exactOp,exactLesson,filing,pupil,sold,served⟩
  refine ⟨S,aperture,loss,passport,bare,exactOp,exactLesson,filing,pupil,sold,served,?_⟩
  have agree:WilsonReceivedCloseFoldedOrdinary.Match R hk D Q π Γ Ψ books ahead disks (S₀) levels school.order
      school.horizon school.pieces hi (head) S bareReturn := by
    intro j mj jb L trail x field lag hl
    obtain ⟨jt,all⟩:=pupil j mj _ L trail
    let n:=R.family.side j per
    let writer:=Oak.student (i:=j) (n:=per) R hk D Q π Γ books mj L.op L.lesson ahead disks L.model school.order L.voter
    have paid:=Air.license writer (fun v=>(writer v).paint x) levels L.w L.issued.earning
      (Poetry.Agenda.stem D φ (Burn.horizon k) (R.alloy.B.a.clock.J j)) (fun v=>L.issued.earning.honor v x)
    let tape₀:=AllOrder.Floe.Step.tape (Burn.horizon k+2)
    have same:=WilsonOriginalCopiedMarkerLayout.same (dvd_refl n.val) writer levels (π (j+1)) (π j) tape₀ x lag field paid
    exact (all x n (dvd_refl _) lag hl field).trans (same.trans (WilsonOriginalSelfPeriod.original writer levels (π j) tape₀ x lag field paid))
  exact WilsonReceivedCloseFoldedOrdinary.original R hk D Q π Γ Ψ books ahead disks (S₀) levels school.order school.horizon
    school.pieces hi (head) simple 3 37 q shape span (U₀) cap height angleCap ε (WilsonReceivedCloseReportedWallet.covers R) hp ep
    S (Nat.lt_succ_self (i+1)) bareReturn history scroll chamber volume stage agree univ _ served close dates

end YM.Integration.WilsonReceivedCloseFoldedThermometer
