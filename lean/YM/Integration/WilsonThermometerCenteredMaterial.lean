import YM.Integration.WilsonThermometerCenteredReentry
import YM.Integration.PhysicalWilsonPeriodizedMaterial

/-! One common unnormalized finite table and one inverse on the actual course,
through the first interacting post at fixed held field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerCenteredMaterial
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

section fixed
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
    {m N per i k : ℕ} (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (tab : D.Tab R.rolls)
    (π : ℕ→Layout G) (Γ : ℕ→Pace.Coin) (Ψ : ∀ j,RG.Rep G (R.family.side j per))
    {φ : ℕ→ℕ} (books : Mentor.Offices.Books D R.rolls tab φ)
    (hi : m ≤ i) (live : i < N) (ahead : Mentor.Forecast D R.rolls tab φ books)
    (order shelf seats : ℕ) (o : Positions (Fin 3) (R.family.side N per))
    (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D tab π Γ Ψ books ahead WilsonThermometerCourseHearing.disks
      sectors levels order shelf seats i hi (offered R A simple live o))
    (angle : Exterior.fieldDir G (R.family.side i per) 1)
local notation "issued" => Air.craft P.model (fun t=>(P.model t).paint fired) levels
  (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
local notation "K" => (RunFormalChain.fromRun R).step N i per live
local notation "raw" F:max t:max => Bulk.Fk (K) F t (issued) angle order
local notation "base" => PhysicalWilsonPeriodizedMaterial.reference R N i per live angle (issued) order
local notation "forest" => Forest (R.family.path.levels.clock.op i per).ratio
local notation "tags" => (R.family.path.levels.clock.op i per).Choices

theorem posted (F : forest) (tag : tags) : raw F tag = base := by
  have legal : Legal (AllOrder.Floe.Step.tape (Burn.horizon k+2)) (π (i+1)) := by
    rw [P.lesson.ticket]
    exact AllOrder.Floe.Step.PlanV.audited R.rolls D _ _ _ P.lesson.entry
  have rows := Air.license P.model (fun a=>(P.model a).paint fired) levels P.w P.salary
    (Poetry.Agenda.stem D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) (fun a=>P.salary.honor a fired)
  exact PhysicalWilsonPeriodizedMaterial.original R N i per live angle (issued) order F tag
    (Air.standard P.model _ levels rows (π (i+1)) _ legal).1

/-- Sum the complete marked prior numerators on their own choices before
dividing by the shared Wilson vacuum. Their proper coefficients may vary
with every tag and forest. -/
theorem group {ι : Type*} (keys : Finset ι) (F : ι→forest) (tag : ι→tags) (prior : ι→Poly J) (g : ℂ) :
    (∑ t∈keys, (total (prior t) (Order.value g (Order.ratio (raw (F t) (tag t))))).part full) =
    (total (∑ t∈keys,prior t) (Order.value g (Order.ratio (base)))).part full := by
  calc
    _ = ∑ t∈keys,(total (prior t) (Order.value g (Order.ratio (base)))).part full := by
      apply sum_congr rfl
      intro t _
      rw [posted R A simple hk D tab π Γ Ψ books hi live ahead order shelf seats o P angle (F t) (tag t)]
    _ = _ := by rw [total,Finset.sum_mul,Poly.part_sum]; rfl
end fixed

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
      (_date : A.station.k=i+1) (_checked : A.station.checked f F A.horizon) (_near : close R A)
      (_shape : op.count=school.pieces) (_size : 3 ≤ school.pieces) (_space : 14 ≤ school.horizon)
      (_room : WilsonOriginalStarSceneWords.maximum R levels ≤ school.order)
      (_stage : school.order+1 ≤ op.stage) (_ranks : 6 ≤ R.alloy.B.a.clock.J (i+1))
      (_script : Sycamore.Boot.need 0 school ≤ R.alloy.B.a.clock.J (i+2))
      (_refs : ∀ j,R.family.ref (levels j) ≤ (i+2))
      (_path : PlanV.Path D R.alloy tab (Burn.horizon k) (i+2) m π Γ) (_pass : Pass D tab R.alloy R.kit)
      (_month : Scholar.Month R.rolls D tab R.alloy.delay) (_fits : school.order ≤ Burn.horizon k+1)
      (_load : school.pieces ≤ Burn.horizon k+2) (_packed : school.order+school.horizon ≤ Burn.horizon k+2),
      ∃ L : WilsonOriginalReceivedChain.Post (N:=i+2) R hk D tab π Γ Ψ books ahead
          WilsonThermometerCourseHearing.disks sectors levels school.order school.horizon school.pieces i hi
          (offered R A simple (Nat.lt_succ_of_lt (Nat.lt_succ_self i)) o),
      let g := Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
      (8*(Oak.expenseReal R hk D tab π Γ books hi L.op L.lesson ahead school.order school.horizon)^school.pieces)*L.rent ≤ ε*g^q ∧
      (∀ s : (J).Mode,g^115≤Poly.toll L.w s) ∧
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
        (∀ (F : Forest (R.family.path.levels.clock.op i per).ratio) (tag : (R.family.path.levels.clock.op i per).Choices),
          Bulk.Fk program F tag bank angle school.order = material) ∧
        ∀ z : ℝ, |z| ≤ |A₀| * (Real.log b)^depth*((B.B:ℝ)^2*B.threshold)/g →
          (∀ e,‖Exterior.collect G angle e‖ ≤ cap*|z|) →
          Poly.price (fun v=>g*L.w v) (inverseMass Q) ≤ C₃ ∧
          g^118 * (∑ s : (J).Mode, ‖weight Q s‖) ≤ C₃ := by
  filter_upwards [WilsonThermometerCenteredReentry.original R simple (f:=f) (F:=F) fund slow D φ width income k school depth A₀ cap hc
      q deep aged ep] with i paid
  intro A m per hk tab π Γ Ψ history law books chamber money hi warm top o op lesson cal ahead hospital date
    checked near shape size space room stage ranks script refs path pass month fits load packed
  obtain ⟨P,_,_,_,_,h,_,L,_,rent,weights,priced⟩ :=
    paid A hk tab π Γ Ψ history law books chamber money hi warm top o op lesson cal ahead hospital date
      checked near shape size space room stage ranks script refs path pass month fits load packed
  refine ⟨L,rent,weights,?_⟩
  intro a B b angle bank program material Q
  have common := posted R A simple hk D tab π Γ Ψ books hi (Nat.lt_succ_of_lt (Nat.lt_succ_self i)) ahead
    school.order school.horizon school.pieces o L angle
  refine ⟨common,?_⟩
  intro z hz inside
  let F₀ := WilsonCoeffUV.repeatF (R.family.path.levels.clock.op i per)
  let t₀ := PhysicalWilsonPeriodizedProgram.branch (R.family.path.levels.clock.op i per)
  have file := priced a z hz inside F₀ t₀
  let g := Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
  let Q' := Order.value (g:ℂ) (Order.ratio (Bulk.Fk program F₀ t₀ bank angle school.order))
  change Poly.price (fun v=>g*L.w v) (inverseMass Q') ≤ C₃ ∧
    g^118*(∑ s : (J).Mode,‖weight Q' s‖) ≤ C₃ at file
  have same : Q'=Q := congrArg (fun Z=>Order.value (g:ℂ) (Order.ratio Z)) (common F₀ t₀)
  exact same ▸ file

end YM.Integration.WilsonThermometerCenteredMaterial
