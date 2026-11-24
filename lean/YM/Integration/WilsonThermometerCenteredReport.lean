import YM.Integration.WilsonThermometerFirstRent
import YM.Integration.WilsonThermometerCenteredMaterial
import YM.Integration.WilsonOriginalThermometerReportedPost
import YM.Integration.WilsonOriginalThermometerReportedRefund

/-! The original report after two inverse transfers carries an explicit
common physical-material inverse on its first inherited post. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerCenteredReport
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor Primitives.GCC.Anchor
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonLimitConstruction WilsonOriginalStarSceneRent WilsonOriginalThermometerMicroscopic
open WilsonThermometerCenteredAlgebra WilsonThermometerCourseHearing
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order
open scoped Classical BigOperators Topology
local notation "J" => Stock.census (Fin 3)
local notation "C₃" => WilsonFiniteOrdinaryInverse.fee J

theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
    {f : Extraction.Order} {F : (Bel R.family.book).Hierarchy}
    {δ : ℝ} {T : Campaign R} {W : Campaign.Pillars R T} (fund : FundedOriginalProperties.{u} simple δ W)
    (slow : WilsonWindowReportingPace.Slow R.kit)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ→ℕ)
    (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
    (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (k : ℕ) (school : Syl.School k) (depth : ℕ) (A₀ cap : ℝ) (hc : 0 ≤ cap)
    (q : ℕ) (deep : 2*(q+1)+8 ≤ school.order) (aged : (q+1)+3 ≤ 3*k+2) {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ i : ℕ in atTop, ∀ (A : Group R.family 6) {m per : ℕ}
      (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m) (tab : D.Tab R.rolls)
      (π : ℕ→Layout G) (Γ : ℕ→Pace.Coin) (Ψ : ∀ j,RG.Rep G (R.family.side j per))
      (_history : Concourse R.alloy R.kit R.T π Γ m (i+2) per k Ψ)
      (law : VowsR.LawScroll G φ) (books : Mentor.Offices.Books D R.rolls tab φ)
      (_chamber : VowsR.Chamber law R.kit D tab books)
      (_money : Volume.Fund D R.rolls tab φ books R.alloy.delay) (hi : m ≤ i)
      (_warm : Spill.Raffle.Warm G D R.alloy.delay φ)
      (_top : Topline (Ψ (i+2)) (R.family.path.levels.clock.forcedAllowance (i+2)))
      (o : Positions (Fin 3) (R.family.side (i+2) per))
      (op : Mentor.Opportunity (R.alloy.B.a.clock.J (i+2)) (R.alloy.B.a.clock.J (i+1)))
      (lesson : Lesson (N:=i+2) R hk D tab π Γ (hi.trans (Nat.le_succ i)))
      (_cal : Oak.Calendar R hk D tab π Γ Ψ (hi.trans (Nat.le_succ i)) (N:=i+2) lesson)
      (ahead : Mentor.Forecast D R.rolls tab φ books)
      (_hospital : MintClock.Hospital D R.rolls tab R.kit.target φ books ahead R.alloy.delay)
      (_date : A.station.k=i) (_checked : A.station.checked f F A.horizon) (_near : close R A)
      (_shape : op.count=school.pieces) (_size : 3 ≤ school.pieces) (_space : 14 ≤ school.horizon)
      (_room : WilsonOriginalStarSceneWords.maximum R levels ≤ school.order)
      (_stage : school.order+1 ≤ op.stage) (_ranks : 6 ≤ R.alloy.B.a.clock.J (i+1))
      (_script : Sycamore.Boot.need 0 school ≤ R.alloy.B.a.clock.J (i+2))
      (_refs : ∀ j,R.family.ref (levels j) ≤ (i+2))
      (_path : PlanV.Path D R.alloy tab (Burn.horizon k) (i+2) m π Γ) (_pass : Pass D tab R.alloy R.kit)
      (_month : Scholar.Month R.rolls D tab R.alloy.delay) (_fits : school.order ≤ Burn.horizon k+1)
      (_load : school.pieces ≤ Burn.horizon k+2) (_packed : school.order+school.horizon ≤ Burn.horizon k+2),
      ∃ P : WilsonOriginalReceivedChain.Post (N:=i+2) R hk D tab π Γ Ψ books ahead WilsonThermometerCourseHearing.disks sectors levels
        school.order school.horizon school.pieces (i+1) (hi.trans (Nat.le_succ i)) (offered R A simple (Nat.lt_succ_self (i+1)) o),
      let gt := Coat.gStep (R.family.path.rep (i+2) per (i+2)).beta
      let g := Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
      let Ω := Oak.expenseReal R hk D tab π Γ books (hi.trans (Nat.le_succ i)) P.op P.lesson ahead school.order school.horizon
      P.rent=gt^(q+1) ∧ P.inputIndex=Empty ∧ P.op=op ∧ P.lesson=lesson ∧
      ∃ h : ℝ, 1≤h ∧ ∃ L : WilsonOriginalReceivedChain.Post (N:=i+2) R hk D tab π Γ Ψ books ahead
          WilsonThermometerCourseHearing.disks sectors levels school.order school.horizon school.pieces i hi
          (offered R A simple (Nat.lt_succ_of_lt (Nat.lt_succ_self i)) o),
      (∀ v,L.w v=P.w v/(Ω^6*h)) ∧
      (8*(Oak.expenseReal R hk D tab π Γ books hi L.op L.lesson ahead school.order school.horizon)^school.pieces)*L.rent ≤ ε*g^q ∧
      (∀ s : (J).Mode,g^157≤Poly.toll L.w s) ∧
      ∀ (a : Stationary.Link G (R.family.side i per)),
        let B := R.family.path.levels.budget i
        let b := R.family.path.levels.clock.hatBeta i
        let angle := Stationary.arm G (R.family.side i per) 1 a
        let bank := Air.craft L.model (fun h=>(L.model h).paint fired) levels
          (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        let program := (RunFormalChain.fromRun R).step (i+2) i per (Nat.lt_succ_of_lt (Nat.lt_succ_self i))
        let material := PhysicalWilsonPeriodizedMaterial.reference R (i+2) i per (Nat.lt_succ_of_lt (Nat.lt_succ_self i))
          angle bank school.order
        let Q := Order.value (g:ℂ) (Order.ratio material)
        (∀ (forest : Forest (R.family.path.levels.clock.op i per).ratio) (tag : (R.family.path.levels.clock.op i per).Choices),
          Bulk.Fk program forest tag bank angle school.order = material) ∧
        ∀ z : ℝ, |z| ≤ |A₀| * (Real.log b)^depth*((B.B:ℝ)^2*B.threshold)/g →
          (∀ e,‖Exterior.collect G angle e‖ ≤ cap*|z|) →
          Poly.price (fun v=>g*L.w v) (inverseMass Q) ≤ C₃ ∧
          g^160 * (∑ s : (J).Mode, ‖weight Q s‖) ≤ C₃ := by
  filter_upwards [WilsonThermometerCenteredCompensation.original R simple D φ width school.order school.horizon
      k school.pieces depth A₀ cap hc, WilsonOriginalThermometerReportedRefund.original R simple,
      (tendsto_add_atTop_nat 1).eventually (WilsonReceivedTaylorWindow.potential R simple 0 0),
      eventually_ge_atTop (WilsonOriginalThermometerReportedPost.opening R simple (f:=f) (F:=F) fund slow),
      eventually_ge_atTop (WilsonThermometerFirstRent.opening R simple q school.order k school.pieces deep aged ep),
      R.alloy.B.a.fits.deep.eventually_ge_atTop (WilsonOriginalThermometerTollBudget.reach R),
      R.alloy.B.a.fits.deep.eventually_ge_atTop k]
    with i inverse refund window late recurz saved active
  intro A m per hk tab π Γ Ψ history law books chamber money hi warm top o op lesson cal ahead hospital date
    checked near shape size space room stage ranks script refs path pass month fits load packed
  let gt := Coat.gStep (R.family.path.rep (i+2) per (i+2)).beta
  have gtp : 0<gt := ActualRunKernelPackets.regulator_pos R (i+2) per (i+2) le_rfl
  have gts : gt≤1 := (window (i+2) per (Nat.lt_succ_self (i+1)) 0 (by simp)).1
  have small : gt^(q+1)≤1 := pow_le_one₀ gtp.le gts
  obtain ⟨P,w,rent,_,_,_,empty,opEq,lessonEq,_⟩ :=
    WilsonOriginalThermometerReportedPost.original R simple A hk D tab π Γ Ψ history law books chamber
      (hi.trans (Nat.le_succ i)) warm top school o op lesson cal ahead hospital fund slow late
      date checked near shape size space room stage ranks script refs (pow_pos gtp _) small
  let Ω := Oak.expenseReal R hk D tab π Γ books (hi.trans (Nat.le_succ i)) P.op P.lesson ahead school.order school.horizon
  let σ := Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+2))
  let E := max 1 ((1+WilsonOriginalThermometerReportedGrading.cap R i 1)*wallet R levels σ)
  have w' : ∀v,P.w v=(E*Ω)⁻¹ := by
    intro v
    dsimp only [Ω]
    rw [opEq,lessonEq]
    exact congrFun w v
  have rich : 1≤Ω := P.issued.Waffle.cool
  have c1 : 1≤E*Ω := one_le_mul_of_one_le_of_one_le (le_max_left _ _) rich
  have spatial := saved.trans ((R.alloy.B.a.fits.mono (show i ≤ i + 2 from Nat.le_add_right i 2)).trans (Nat.le_succ _))
  have yc : Burn.horizon k ≤ R.alloy.B.a.clock.J (i+2) := (Nat.le_add_right _ _).trans
    (hk.trans (R.alloy.B.a.fits.mono (hi.trans (show i ≤ i + 2 from Nat.le_add_right i 2))))
  have price := WilsonOriginalThermometerReportedToll.original R simple D φ income i (Burn.horizon k)
    yc spatial (zero_le_one.trans rich) P.issued.Beamwork
  have narrow : school.horizon ≤ R.alloy.B.a.clock.J i := (Nat.le_add_left _ _).trans
    (packed.trans (hk.trans (R.alloy.B.a.fits.mono hi)))
  obtain ⟨h,hp,L,wallet,rated,capH⟩ := WilsonThermometerFirstRent.original R A simple (Nat.lt_succ_self (i+1)) o
    hk D tab π Γ Ψ books ahead school.order school.horizon school.pieces hi P refs history path pass law chamber
    month hospital fits narrow load packed q deep aged ep recurz rent.le
  have full := (refund per (E*Ω) Ω h (P.rent+gt^(q+1)) (zero_lt_one.trans_le c1) price rich
    P.issued.Beamwork hp capH (by rw [rent]; linarith only [small]) P.w L.w w' wallet).2
  refine ⟨P,rent,empty,opEq,lessonEq,h,hp,L,wallet,rated,full,?_⟩
  intro a B b angle bank program material Q
  have common := WilsonThermometerCenteredMaterial.posted R A simple hk D tab π Γ Ψ books hi
    (Nat.lt_succ_of_lt (Nat.lt_succ_self i)) ahead school.order school.horizon school.pieces o L angle
  refine ⟨common,?_⟩
  intro z hz inside
  let F₀ := WilsonCoeffUV.repeatF (R.family.path.levels.clock.op i per)
  let t₀ := PhysicalWilsonPeriodizedProgram.branch (R.family.path.levels.clock.op i per)
  obtain ⟨paid,faces⟩ := inverse A hk active tab π Γ Ψ history books law chamber money hi
    (Nat.lt_succ_of_lt (Nat.lt_succ_self i)) o ahead L a z hz inside F₀ t₀
  let g := Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
  let Q' := Order.value (g:ℂ) (Order.ratio (Bulk.Fk program F₀ t₀ bank angle school.order))
  have fee : Poly.price (fun v=>g*L.w v) (inverseMass Q') ≤ C₃ ∧
    g^160*(∑ s : (J).Mode,‖weight Q' s‖) ≤ C₃ := ⟨paid,faces 157 full⟩
  have same : Q'=Q := congrArg (fun Z=>Order.value (g:ℂ) (Order.ratio Z)) (common F₀ t₀)
  exact same ▸ fee

end YM.Integration.WilsonThermometerCenteredReport
