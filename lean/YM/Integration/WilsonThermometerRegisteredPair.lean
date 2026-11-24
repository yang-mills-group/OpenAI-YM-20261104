import YM.Integration.WilsonThermometerRegisteredStation
import YM.Integration.WilsonOriginalCoveredSignedReceipt
import YM.Integration.WilsonThermometerTestedReturn

/-! The first two measured blockings of the signed thermometer with one scalar source deleted.
The finite test panels use the same pre-enrolled numerical columns on all auxiliary copies. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredPair
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


open WilsonOriginalReceivedChain Laurent Stationary Comparison.RG02 Comparison.RG02.Order
open WilsonThermometerCourseIntake

/-- Turn off one scalar in the full three-source portfolio. -/
def without (t : Fin 3) : Wallet WilsonThermometerCourseHearing.disks :=
  fun v => ⟨if v=t then 0 else 1, by split  <;> simp [WilsonThermometerCourseHearing.disks]⟩

theorem face {N b n : ℕ} (positions : Positions (Fin 3) (R.family.side N n)) (live : b < N)
    (t : Fin 3) (s : (J₀).Mode) (W : Config G (R.family.side (b+1) n)) :
    (WilsonThermometerCourseHearing.offered R A simple live positions (without t) W).part s =
      if t ∈ s.val then 0 else (incoming R A simple live positions W).part s := by
  change (∏ v ∈ s.val, (without t v).val) * _ = _
  by_cases ht : t ∈ s.val
  · rw [if_pos ht,Finset.prod_eq_zero ht (by simp [without]),zero_mul]
  · simp only [if_neg ht]
    have one : ∀ v ∈ s.val, (without t v).val=1 := by
      intro v member
      have ne : v ≠ t := fun eq => ht (eq ▸ member)
      simp [without,ne]
    rw [Finset.prod_eq_one one,one_mul]

variable
  (strip : ∀ x k : ℕ, k ≤ x → ∀ b : ℝ, R.alloy.delay.betaEntry x ≤ b →
    Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹ ^ 2) ≤ b)
  (q depth : ℕ) (deep:2*(q+1)+8 ≤ school.order) (aged:q+4 ≤ 3*k+2)
  (H cap:ℝ) (cap_pos:0 ≤ cap) {ε:ℝ} (ep:0 < ε)

/-- The stationary comparison menu is fixed before the physical period and the three sites. -/
def opening : ℕ := (eventually_atTop.mp (WilsonOriginalCoveredSignedReceipt.original R simple D φ strip
  levels 0 q depth school.order school.horizon k school.pieces deep aged H cap cap_pos ep)).choose

local notation "earlier" => (show i < i+2 from by omega)
local notation "first" => (Nat.lt_succ_self (i+1))
local notation "input" => WilsonReceivedCloseHistory.history (N:=i+2) R disks (head) i (Nat.le_succ i)
local notation "second" => WilsonThermometerCourseHearing.offered R A simple (earlier) o
local notation "g₁" => Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
local notation "g₂" => Coat.gStep (R.family.path.rep (i+2) per (i+2)).beta
local notation "fields" => Config G (R.family.side i per)
local notation "tab" x:max F:max => WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o x F
local notation "stage" => ((Advent.budgetR R i)^2*(Advent.budgetR R (i+1))^7)

include history scroll chamber warm top cal hospital fund slow in
/-- The real nonbare post, its two-date monetary payment and its signed comparison to the
independent response on the deposited first block. The returned post retains its full old hard family. -/
theorem original (late:WilsonOriginalThermometerReportedPost.opening R simple (f:=f) (F:=F) fund slow ≤ i)
    (date:A.station.k=i) (checked:A.station.checked f F A.horizon) (near:close R A)
    (shape:op.count=school.pieces) (size:3 ≤ school.pieces) (space:14 ≤ school.horizon)
    (room:WilsonOriginalStarSceneWords.maximum R levels ≤ school.order)
    (opStage:school.order+1 ≤ op.stage) (ranks:6 ≤ R.alloy.B.a.clock.J (i+1))
    (width:Sycamore.Boot.need 0 school ≤ R.alloy.B.a.clock.J (i+2))
    (refs:∀ v,R.family.ref (levels v) ≤ i+2) {τ:ℝ} (pos:0 < τ) (bounded:τ ≤ 1)
    (floor:m ≤ i) (fit:k ≤ R.alloy.B.a.clock.J i)
    (path:PlanV.Path D R.alloy Q (Burn.horizon k) (i+2) m π Γ)
    (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (fits:school.order ≤ Burn.horizon k+1) (shelved:school.horizon ≤ R.alloy.B.a.clock.J m)
    (load:school.pieces ≤ Burn.horizon k+2) (packed:school.order+school.horizon ≤ Burn.horizon k+2)
    (unit:ε ≤ 1)
    (tender:WilsonReceivedMeasuredStampPrice.opening R simple q school.order k
      (show 2*q+8 ≤ school.order from by omega) (show q+3 ≤ 3*k+2 from by omega) ep ≤ m+1)
    (heard:opening R simple D school strip q depth deep aged H cap cap_pos ep ≤ i)
    (small:∀ j,m ≤ j → j ≤ i+2 → 0 < Coat.gStep (R.family.path.rep (i+2) per j).beta ∧
      Coat.gStep (R.family.path.rep (i+2) per j).beta ≤ 1) :
    ∃ (P:Post (N:=i+2) R hk D Q π Γ Ψ books ahead disks S₀ levels school.order school.horizon
      school.pieces i floor (input)) (d:ℝ), 1 ≤ d ∧ d ≤ stage ∧ (∀ v,P.w v=w₁ v/d) ∧
      P.rent ≤ τ+ε*g₂^q ∧
      ∀ t:Fin 3, ∀ (a:Stationary.Link G (R.family.side i per)),
      let B:=R.family.path.levels.budget i
      let b:=R.family.path.levels.clock.hatBeta i
      let Ω:=Oak.expenseReal R hk D Q π Γ books floor P.op P.lesson ahead school.order school.horizon
      let angle:=Stationary.arm G (R.family.side i per) 1 a
      ∀ z:ℝ, |z| ≤ |H| * (Real.log b)^depth * ((B.B:ℝ)^2 * B.threshold)/g₁ →
        (∀ e, ‖Exterior.collect G angle e‖ ≤ cap * |z|) →
        let W:=Integral.sample g₁ angle
        flags (Ψ i).p.threshold W=∅ →
        let read:=Order.logTo 3 ((((Ψ i).eval W:ℂ)⁻¹) •
          LocalComparison.actualPush R.family (i+2) per i ((second) (without t)) W)
        let bare:=WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o (without t)
        let formal:=WilsonOriginalCoveredEvolution.run R first π Γ (Burn.horizon k+2) school.order levels bare
        let target:=WilsonCoherentMayerWindingGrades.panel school.order (g₁:ℂ)
          (fun e=>formal i (Nat.le_succ i) _ (dvd_refl _) e a)
        Poly.price P.w (read-target) ≤ (Fintype.card (J₀).Mode : ℝ)*
          ((8*Ω^school.pieces)*P.rent)+ε*g₁^q := by
  obtain ⟨U,win,fee,_,_,_,_,_,_,_,_,_,entry⟩ :=
    WilsonThermometerRegisteredStation.original R simple A hk D Q π Γ Ψ history scroll books chamber hi
      warm top school o op lesson cal ahead hospital fund slow late date checked near shape size space
      room opStage ranks width refs pos bounded
  obtain ⟨P,d,dpos,dmax,move,cost,_,trail⟩ :=
    WilsonReceivedCloseHistory.descent R hk D Q π Γ Ψ books ahead disks S₀ levels school.order
      school.horizon school.pieces hi (head) U history path first pass scroll chamber month hospital
      fits shelved load packed simple q (by omega) (by omega) ep unit tender
      WilsonThermometerCourseHearing.fired small i (Nat.le_succ i) floor
  have moved : input = second := by
    rw [←WilsonReceivedCloseHistory.adjacent (N:=i+2) R disks (head) (Nat.lt_succ_self i),
      WilsonReceivedCloseHistory.head (N:=i+2) R disks (head)]
    exact WilsonThermometerTestedReturn.push R A simple first o refs
  refine ⟨P,d,dpos,?_,?_,?_,?_⟩
  · simpa using dmax
  · intro v; simpa only [win] using move v
  · simpa [fee,Pert.Asymptotics.regulatorRun,Coat.gStep] using cost
  · intro t
    have issued:=(eventually_atTop.mp (WilsonOriginalCoveredSignedReceipt.original R simple D φ strip
      levels 0 q depth school.order school.horizon k school.pieces deep aged H cap cap_pos ep)).choose_spec i heard
      (m:=m) (N:=i+2) (per:=per)
    obtain ⟨ib,read⟩:=issued hk fit Q π Γ Ψ history books floor earlier ahead disks S₀ input P (without t)
      hi first (head) U (WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o (without t))
      pass month fits shelved (entry (without t)) trail
    intro a
    simpa only [moved,Fintype.card_fin] using read a

end YM.Integration.WilsonThermometerRegisteredPair
