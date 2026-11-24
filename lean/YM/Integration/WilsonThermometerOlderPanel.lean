import YM.Integration.WilsonJointAxialRefund
import YM.Integration.WilsonThermometerCenteredWeight
import YM.Integration.WilsonThermometerCenteredReport

/-! The true nominated (6,4,4) reporting post and its frozen inverse on the older
Wilson marginal. All three independent fine positions are chosen after the onset. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerOlderPanel
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

open WilsonJointAxialRoster WilsonJointAxialHearing WilsonRegisteredAffineHalo WilsonRegisteredAxialRates
open WilsonRootedKioskOccupiedSlip WilsonReportingForestAngularFare Push.AbsoluteSums OPE.Therm
open MSbar.Heath Extra.Trajectories Multi ConnectedActivityE6.SliceRows

theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
    {f : Extraction.Order} {F : (Bel R.family.book).Hierarchy}
    {δ : ℝ} {T : Campaign R} {W : Campaign.Pillars R T} (fund : FundedOriginalProperties.{u} simple δ W)
    (slow : WilsonWindowReportingPace.Slow R.kit)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ→ℕ)
    (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
    (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (k : ℕ) (school : Syl.School k) (depth : ℕ) (A₀ cap : ℝ) (hc : 0 ≤ cap)
    (voice : Voice G) (clear : Clear G voice) (axes : Lattice.Order)
    (gate : WilsonReportingForestAngularReflection.posted R) (p q : ℕ)
    (reserve : p+164 ≤ q) (deep : 2*(q+1)+8 ≤ school.order) (aged : (q+1)+3 ≤ 3*k+2) {ε : ℝ} (ep : 0 < ε) (fraction : ε*((3:ℝ)^q+2) ≤ 1) :
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
      (_load : school.pieces ≤ Burn.horizon k+2) (_packed : school.order+school.horizon ≤ Burn.horizon k+2)
      (_shelf : school.horizon ≤ R.alloy.B.a.clock.J i) (_fit : k ≤ R.alloy.B.a.clock.J i),
      ∃ L : WilsonOriginalReceivedChain.Post (N:=i+2) R hk D tab π Γ Ψ books ahead
        WilsonThermometerCourseHearing.disks sectors levels school.order school.horizon school.pieces i hi
        (offered R A simple (Nat.lt_succ_of_lt (Nat.lt_succ_self i)) o),
        let g := Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
        let n := school.order+school.horizon+2
        let K := p+161+2*n*3
        let Ω := Oak.expenseReal R hk D tab π Γ books hi L.op L.lesson ahead school.order school.horizon
        8*Ω^school.pieces*L.rent ≤ ε*g^q ∧
        ∀ (a : Stationary.Link G (R.family.side i per)) (z : ℝ),
          let B := R.family.path.levels.budget i
          let b := R.family.path.levels.clock.hatBeta i
          let probe := Stationary.arm G (R.family.side i per) 1 a
          |z| ≤ |A₀| *(Real.log b)^depth*((B.B:ℝ)^2*B.threshold)/g →
          (∀ e, ‖Exterior.collect G probe e‖ ≤ cap * |z|) →
          let tape := AllOrder.Floe.Step.tape (Burn.horizon k+2)
          let bank := Air.craft L.model (fun h=>(L.model h).paint fired) levels (π (i+1)) tape
          let Q := Order.value (g:ℂ) (Order.ratio (PhysicalWilsonPeriodizedMaterial.reference R (i+2) i per
              (by omega) probe bank school.order))
          g^160*(∑ s : (J).Mode,‖weight Q s‖/Poly.toll L.w s) ≤ C₃ ∧
          let op₀ := R.family.path.levels.clock.op i per
          let placed := L.passport.coarser op₀.ratio
          let H := radius R (invoice 3 (q+2*n)) 1 i
          let r := amplitude R voice H (i+2) per i
          let height := (WilsonDegreeFourInheritedRange.height R (q+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1
          let cold := House.chilly (G:=G) (plaquettes placed.origin H) (angularCut b)
          let schoolman := Oak.student (n:=per) R hk D tab π Γ books hi L.op L.lesson ahead
            WilsonThermometerCourseHearing.disks L.model school.order L.voter
          let lamps := rendered schoolman (Ψ i).p (Coat.gStep (Ψ (i+1)).beta)
          ∀ (forest : Forest op₀.ratio) (tag : op₀.Choices) (j : ℕ) (age : j ≤ i),
            let model := fun U => Order.value (g:ℂ) (Order.ratio (Bulk.Fk
              ((RunFormalChain.fromRun R).step (i+2) i per (by omega)) forest tag bank
              (angleOf placed.origin height voice axes r g U) school.order))
            let delta := fun U => ∑ s : (J).Mode,weight Q s *
              ((Poly.pass (bare lamps fired U)).part s-cold.indicator (fun field=>(model field).part s) U)
            ∫ Z, ‖actualTransport R.family (N:=i+2) delta age Z‖ ∂scene R.family.path (i+2) per j ≤
              C₃*(WilsonReceivedCloseOrdinaryGrade.invoice (J) 3 0 (p+160) 1+
                (4:ℝ)^K*(Fintype.card (Multi.parts (J)).Mode)*((2:ℝ)^n)^3)*g^(p+1) := by
  let n:=school.order+school.horizon+2
  let K:=p+161+2*n*3
  filter_upwards [WilsonThermometerCenteredReport.original R simple (f:=f) (F:=F) fund slow D φ width income
      k school depth A₀ cap hc q deep aged ep,
    eventually_ge_atTop (max (WilsonJointAxialRoster.opening R simple fund slow.2 voice clear 3 n q ep)
      (WilsonReceivedAxialFiling.opening R simple D φ width school.order school.horizon 3 ep)),
    eventually_ge_atTop (max (WilsonReceivedAxialFinite.opening R simple q ep)
      (WilsonReceivedAxialFinite.massOpening R D levels school.order school.horizon school.pieces (k:=k) simple width)),
    eventually_ge_atTop (WilsonJointAxialScalar.opening (V:=Fin 3) R simple gate q n K),
    eventually_ge_atTop (eventually_atTop.mp (WilsonJointAxialClock.original R simple)).choose] with i received late finiteLate rareLate clockLate
  intro A m per hk tab π Γ Ψ history law books chamber money hi warm top o op lesson cal ahead hospital
    date checked near shape size space room stage ranks script refs path pass month fits load packed shelf fit
  obtain ⟨P,_,_,_,_,factor,_,L,_,rent,roof,read⟩ := received A hk tab π Γ Ψ history law books chamber
    money hi warm top o op lesson cal ahead hospital date checked near shape size space room stage ranks script
    refs path pass month fits load packed
  refine ⟨L,rent,?_⟩
  intro a z B b probe hz inside tape bank Q
  have statement := read a
  have mass := (statement.2 z hz inside).1
  obtain ⟨gp,small,_,_⟩ := (eventually_atTop.mp (WilsonJointAxialClock.original R simple)).choose_spec i clockLate (i+2) per (by omega)
  have restored := WilsonThermometerCenteredWeight.original Q L.w L.salary.positive gp small 157 (roof full) mass
  refine ⟨restored,?_⟩
  intro op₀ placed H r height cold schoolman lamps forest tag j age model delta
  have slot : p+160+1+Fintype.card (Fin 3) ≤ q := by simpa only [Fintype.card_fin] using reserve
  have head : q ≤ school.order := by omega
  have counted : L.op.count ≤ Burn.horizon k+2 := L.capacity.le.trans load
  have given := WilsonJointAxialRefund.original R hk D tab π Γ Ψ history books hi
    (Nat.lt_succ_of_lt (Nat.lt_succ_self i)) ahead WilsonThermometerCourseHearing.disks sectors levels
    school.order school.horizon school.pieces (offered R A simple (Nat.lt_succ_of_lt (Nat.lt_succ_self i)) o) L
    simple fund slow.2 voice clear axes q ep width law chamber money late finiteLate pass hospital shelf counted fit
    gate p 160 slot head fraction clockLate rareLate fired forest tag univ (weight Q) C₃ restored j age
  exact given

end YM.Integration.WilsonThermometerOlderPanel
