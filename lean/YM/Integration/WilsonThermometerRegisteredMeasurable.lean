import YM.Integration.WilsonThermometerRegisteredTrace
import YM.Integration.WilsonThermometerRegisteredCompact
import YM.Integration.WilsonThermometerRegisteredWindow

/-! Comparison with the declared numerical material at the joint axial chart of the measured field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredMeasurable
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
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+2)) (R.alloy.B.a.clock.J (i+1)))
  (lesson:Lesson (N:=i+2) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=i+2) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+2))
local notation "S₀" => WilsonThermometerCourseHearing.sectors
local notation "P₀" => Ψ (i+2)
local notation "J₀" => Stock.census (Fin 3)
local notation "Ω₀" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead school.order school.horizon

variable {f:Extraction.Order} {F:(Bel R.family.book).Hierarchy} {δ:ℝ} {T:Campaign R}
  {W:Campaign.Pillars R T} (fund:FundedOriginalProperties.{u} simple δ W) (slow:WilsonWindowReportingPace.Slow R.kit)

open FVA1Physical.TwoReset

local notation "E₁" => max 1 ((1+WilsonOriginalThermometerReportedGrading.cap R i 1)*wallet R levels σ₀)
local notation "w₁" => (fun _:Fin 3 => ((E₁)*(Ω₀))⁻¹)


open WilsonOriginalReceivedChain Laurent Stationary Comparison.RG02 Comparison.RG02.Order
open WilsonThermometerCourseIntake

variable
  (strip : ∀ x k : ℕ, k ≤ x → ∀ b : ℝ, R.alloy.delay.betaEntry x ≤ b →
    Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹ ^ 2) ≤ b)
  (q depth : ℕ) (deep:2*(q+1)+8 ≤ school.order) (aged:q+4 ≤ 3*k+2)
  (H cap:ℝ) (cap_pos:0 ≤ cap)

open WilsonThermometerRegisteredPair OriginalForcedAddresses Extra.Trajectories
open WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading

local notation "earlier" => (show i < i+2 from by omega)
local notation "first" => (Nat.lt_succ_self (i+1))
local notation "g₁" => Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
local notation "g₂" => Coat.gStep (R.family.path.rep (i+2) per (i+2)).beta
local notation "stage" => ((Advent.budgetR R i)^2*(Advent.budgetR R (i+1))^7)


open WilsonOriginalThermometerTollBudget
local notation "K₀" => WilsonThermometerRegisteredOrdinary.gross R simple (f:=f) (F:=F) fund slow
local notation "e₀" => WilsonThermometerRegisteredOrdinary.power R simple (f:=f) (F:=F) fund slow
local notation "crop" => (E₁)*(Ω₀)


open WilsonThermometerRegisteredRate WilsonThermometerRegisteredCells WilsonThermometerAlignedCells
open MeasureTheory OPE OPE.Orbits XSpace.Rose Push.GridApprox

local notation "T₀" => Site (R.family.side (i+2) per)
local notation "N₀" => ((i+2,per):RG12.UVIndex)


open Ac OPE.Therm Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open RG16 MSbar.Heath
open WilsonRootedKioskOccupiedSlip WilsonRegisteredAffineHalo WilsonRegisteredAxialRates
open WilsonReportingForestAngularFare WilsonJointAxialRoster
open Multi Comparison.RG02.Cumulants WilsonIndependentOrdinaryPairGrade

local notation "degreeCap" => (school.order+school.horizon+2)

open private small from YM.Integration.WilsonThermometerRegisteredRate

include history scroll chamber warm top cal hospital fund slow in
/-- The explicitly computed two-date pair is continuous in the lower held link.
The filed bank equals its actual registered student on every link. -/
theorem original (late:WilsonOriginalThermometerReportedPost.opening R simple (f:=f) (F:=F) fund slow ≤ i)
    (date:A.station.k=i) (checked:A.station.checked f F A.horizon) (near:close R A)
    (shape:op.count=school.pieces) (size:3 ≤ school.pieces) (space:14 ≤ school.horizon)
    (room:WilsonOriginalStarSceneWords.maximum R levels ≤ school.order)
    (opStage:school.order+1 ≤ op.stage) (ranks:6 ≤ R.alloy.B.a.clock.J (i+1))
    (width:Sycamore.Boot.need 0 school ≤ R.alloy.B.a.clock.J (i+2))
    (refs:∀ v,R.family.ref (levels v) ≤ i+2)
    (floor:m ≤ i)
    (path:PlanV.Path D R.alloy Q (Burn.horizon k) (i+2) m π Γ)
    (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (fits:school.order ≤ Burn.horizon k+1) (shelved:school.horizon ≤ R.alloy.B.a.clock.J m)
    (load:school.pieces ≤ Burn.horizon k+2) (packed:school.order+school.horizon ≤ Burn.horizon k+2)
    (tender:WilsonReceivedMeasuredStampPrice.opening R simple q school.order k
      (show 2*q+8 ≤ school.order from by omega) (show q+3 ≤ 3*k+2 from by omega) zero_lt_one ≤ m+1)
    (heat:warmDate R simple ≤ m) (y:T₀×T₀) (t a b:Fin 3) :
    Continuous (fun link:Stationary.Link G (R.family.side i per) =>
      WilsonThermometerRegisteredCompact.prescribed R A π Γ school t a b link y) := by
  let o:=placement (R:=R) (N₀) y
  let x:=without t
  let head:=WilsonThermometerCourseHearing.offered R A simple first o
  have small₁:=small R simple heat
  have cash:=small₁ (i+2) (i+2) per (by omega) le_rfl
  have pos : 0 < g₂^q:=pow_pos cash.1 _
  have bounded : g₂^q ≤ 1:=pow_le_one₀ cash.1.le cash.2
  obtain ⟨U,_,_,_,_,_,_,_,_,_,_,_,entry⟩ :=
    WilsonThermometerRegisteredStation.original R simple A hk D Q π Γ Ψ history scroll books chamber hi
      warm top school o op lesson cal ahead hospital fund slow late date checked near shape size space
      room opStage ranks width refs pos bounded
  obtain ⟨P,d,_,_,_,_,_,trail⟩ :=
    WilsonReceivedCloseHistory.descent R hk D Q π Γ Ψ books ahead WilsonThermometerCourseHearing.disks S₀ levels school.order
      school.horizon school.pieces hi head U history path first pass scroll chamber month hospital
      fits shelved load packed simple q (by omega) (by omega) (ε:=1) zero_lt_one le_rfl tender
      WilsonThermometerCourseHearing.fired (fun j mj jN=>small₁ j (i+2) per mj jN) i (Nat.le_succ i) floor
  let bare₀ := WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o x
  obtain ⟨ib, filed⟩ := WilsonOriginalCoveredHearing.evaluated R hk D Q π Γ Ψ books ahead WilsonThermometerCourseHearing.disks S₀ levels
    school.order school.horizon school.pieces hi head U x bare₀ first history pass month fits shelved (entry x) trail
  let student:=Oak.student (n:=per) R hk D Q π Γ books floor P.op P.lesson ahead WilsonThermometerCourseHearing.disks P.model school.order P.voter
  let bank:=Air.craft student (fun j=>(student j).paint x) levels (π i) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
  let n:=R.family.side i per
  let filedRow (z:Stationary.Link G n):=WilsonCoherentMayerWindingGrades.panel school.order (g₁:ℂ)
    (fun d=>Air.discharge bank d (Stationary.arm G n 1 z))
  have each (s:(J₀).Mode) : Continuous (fun z:Stationary.Link G n => (filedRow z).part s) :=
    (WilsonThermometerRegisteredTrace.panel bank school.order (g₁:ℂ) s).comp (Stationary.arm G n 1).continuous
  have eq (z:Stationary.Link G n):WilsonThermometerRegisteredCompact.prescribed R A π Γ school t a b z y =
      (filedRow z).part ⟨{a,b},mem_univ _⟩+(filedRow z).part ((J₀).fire a)*(filedRow z).part ((J₀).fire b):=by
    unfold WilsonThermometerRegisteredCompact.prescribed
    simp only [←WilsonThermometerNumericalStation.returned R A D π Γ (φ:=φ) school
      (placement (R:=R) (N₀) y) (without t)]
    rw [filed (g₁:ℂ) z]
  exact ((each ⟨{a,b},mem_univ _⟩).add ((each ((J₀).fire a)).mul (each ((J₀).fire b)))).congr
    (fun z=> (eq z).symm)

end YM.Integration.WilsonThermometerRegisteredMeasurable
