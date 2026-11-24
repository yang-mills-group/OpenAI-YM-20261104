import YM.Integration.WilsonThermometerRegisteredOrdinary

/-! The ordinary Wilson pair from two real blockings on every filed cell position and protected probe. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredDetector
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

variable
  (strip : ∀ x k : ℕ, k ≤ x → ∀ b : ℝ, R.alloy.delay.betaEntry x ≤ b →
    Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹ ^ 2) ≤ b)
  (q depth : ℕ) (deep:2*(q+1)+8 ≤ school.order) (aged:q+4 ≤ 3*k+2)
  (H cap:ℝ) (cap_pos:0 ≤ cap) {ε:ℝ} (ep:0 < ε)

open WilsonThermometerRegisteredPair OriginalForcedAddresses Extra.Trajectories
open WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading

local notation "earlier" => (show i < i+2 from by omega)
local notation "first" => (Nat.lt_succ_self (i+1))
local notation "input" => WilsonReceivedCloseHistory.history (N:=i+2) R disks (head) i (Nat.le_succ i)
local notation "second" => WilsonThermometerCourseHearing.offered R A simple (earlier) o
local notation "g₁" => Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
local notation "g₂" => Coat.gStep (R.family.path.rep (i+2) per (i+2)).beta
local notation "stage" => ((Advent.budgetR R i)^2*(Advent.budgetR R (i+1))^7)

include history scroll chamber warm top cal hospital fund slow in
/-- The ordinary protected two-field measurement includes the two singleton terms
and their common older Wilson prior. All grade-dependent prices are chosen before the period. -/
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
    (held:0 < i) (fieldDate:WilsonThermometerRegisteredOrdinary.opening R simple (f:=f) (F:=F) fund slow ≤ i)
    (heard:WilsonThermometerRegisteredPair.opening R simple D school strip q depth deep aged H cap cap_pos ep ≤ i)
    (small:∀ j,m ≤ j → j ≤ i+2 → 0 < Coat.gStep (R.family.path.rep (i+2) per j).beta ∧
      Coat.gStep (R.family.path.rep (i+2) per j).beta ≤ 1) :
    ∃ (P:Post (N:=i+2) R hk D Q π Γ Ψ books ahead disks S₀ levels school.order school.horizon
      school.pieces i floor (input)) (d:ℝ), 1 ≤ d ∧ d ≤ stage ∧ (∀ v,P.w v=w₁ v/d) ∧
      P.rent ≤ τ+ε*g₂^q ∧
      ∀ t a b:Fin 3, a≠b → a≠t → b≠t → ∀ link:Stationary.Link G (R.family.side i per),
      let B:=R.family.path.levels.budget i
      let β:=R.family.path.levels.clock.hatBeta i
      let Ω:=Oak.expenseReal R hk D Q π Γ books floor P.op P.lesson ahead school.order school.horizon
      let angle:=Stationary.arm G (R.family.side i per) 1 link
      ∀ z:ℝ, |z| ≤ |H| * (Real.log β)^depth * ((B.B:ℝ)^2*B.threshold)/g₁ →
        (∀ e, ‖Exterior.collect G angle e‖ ≤ cap * |z|) →
        let W:=Integral.sample g₁ angle
        flags (Ψ i).p.threshold W=∅ →
        let fields:=fun v:Fin 3 => R.family.O (i+2) per
          (A.station.wheel.atCut (i+2,per) (index A (grade v)) (vector A univ v)) (o.origin v)
        let two:=actualTransport R.family (N:=i+2) (fun U=>fields a U*fields b U) (earlier).le W
        let bare:=WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o (without t)
        let formal:=WilsonOriginalCoveredEvolution.run R first π Γ (Burn.horizon k+2) school.order levels bare
        let target:=WilsonCoherentMayerWindingGrades.panel school.order (g₁:ℂ)
          (fun e=>formal i (Nat.le_succ i) _ (dvd_refl _) e link)
        let s:(J₀).Mode:=⟨{a,b},mem_univ _⟩
        let fee:=(Fintype.card (J₀).Mode:ℝ)*((8*Ω^school.pieces)*P.rent)+ε*g₁^q
        let K:=WilsonThermometerRegisteredOrdinary.gross R simple (f:=f) (F:=F) fund slow
        let e:=WilsonThermometerRegisteredOrdinary.power R simple (f:=f) (F:=F) fund slow
        Poly.toll P.w s*‖two-(target.part s+target.part ((J₀).fire a)*target.part ((J₀).fire b))‖ ≤
          fee*(1+2*(K*β^e)+fee) := by
  obtain ⟨P,d,one,capd,w,price,table⟩:=WilsonThermometerRegisteredPair.original R simple A
    hk D Q π Γ Ψ history scroll books chamber hi warm top school o op lesson cal ahead hospital
    fund slow strip q depth deep aged H cap cap_pos ep late date checked near shape size space room
    opStage ranks width refs pos bounded floor fit path pass month fits shelved load packed unit tender heard small
  have rich : 1 ≤ Ω₀ := (by norm_num : (1:ℝ)≤4).trans (MintClock.Page.roofers ..)
  have unitPaid : 1 ≤ (E₁)*(Ω₀) := one_le_mul_of_one_le_of_one_le (le_max_left _ _) rich
  have test (v:Fin 3) : P.w v ≤ 1 := by
    rw [w v]
    exact (div_le_self (inv_nonneg.mpr (zero_le_one.trans unitPaid)) one).trans (inv_le_one_of_one_le₀ unitPaid)
  refine ⟨P,d,one,capd,w,price,?_⟩
  intro t a b ab at' bt' link B β Ω angle z sizez fitsz W healthy fields two bare formal target s fee K e
  let Y:=WilsonThermometerRegisteredOrdinary.conditional R simple A earlier o t W
  have law : (Ψ i).eval=(R.family.path.rep (i+2) per i).eval := (history.1.walk i floor (earlier).le).view
  have paid : Poly.price P.w (Order.logTo 3 Y-target) ≤ fee := by
    simpa only [Y,WilsonThermometerRegisteredOrdinary.conditional,law] using table t link z sizez fitsz healthy
  have no : t∉s.val := by simpa only [s,mem_insert,mem_singleton,not_or] using And.intro (Ne.symm at') (Ne.symm bt')
  have ordinary : Y.part s=two := by
    rw [show Y.part s = _ from WilsonThermometerRegisteredOrdinary.observed R simple A earlier o held refs t W s,
      if_neg no,WilsonThermometerCourseResidual.observed R A simple (earlier).le o refs W s]
    simp [two,s,fields,prod_insert,ab]
  have boundedLeg (v:Fin 3) : P.w v*‖Y.part ((J₀).fire v)‖ ≤ K*β^e :=
    (mul_le_of_le_one_left (norm_nonneg _) (test v)).trans
      (WilsonThermometerRegisteredOrdinary.singleton R simple A (N:=i+2) (f:=f) (F:=F) fund slow fieldDate held
        date checked near o refs t v W)
  rw [←ordinary]
  exact WilsonThermometerRegisteredOrdinary.pair Y target P.w P.salary.positive
    (WilsonThermometerRegisteredOrdinary.quiet R simple A earlier o held refs t W) paid
    a b s ab rfl (boundedLeg a) (boundedLeg b)

end YM.Integration.WilsonThermometerRegisteredDetector
