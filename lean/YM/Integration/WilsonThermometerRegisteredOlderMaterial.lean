import YM.Integration.WilsonThermometerRegisteredAllWeighted
import YM.Integration.WilsonThermometerOlderPanel

/-! The normalized older Wilson integral on the appointed post. The actual rendered
ordinary source is compared to the independently declared two-date response, with the same
inverse at the same probe and the original angular exclusion throughout. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredOlderMaterial

open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Ac OPE.Therm WilsonLimitConstruction RG16 MSbar.Heath Labels Source Pert.Asymptotics
open WilsonRootedKioskOccupiedSlip WilsonRegisteredAffineHalo WilsonRegisteredAxialRates
open WilsonReportingForestAngularFare WilsonJointAxialRoster
open Multi Extra.Trajectories Comparison.RG02.Cumulants WilsonIndependentOrdinaryPairGrade
open FVA1 Cells Extraction Table Climb Trace Trace.Pilot
open WilsonPositionThermometerCapStation WilsonOriginalThermometerPalette WilsonOriginalThermometerMicroscopic
open WilsonThermometerCourseHearing WilsonThermometerRegisteredPair WilsonPositionThermometerGradedReading
open WilsonPositionThermometerGradedSource
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m i per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m (i+2) per k Ψ)
  {φ:ℕ → ℕ} (books:Mentor.Offices.Books D R.rolls Q φ) (hi:m ≤ i)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (school:Syl.School k) (o:Positions (Fin 3) (R.family.side (i+2) per))
local notation "cut" => (Nat.lt_succ_of_lt (Nat.lt_succ_self i))
local notation "faces" => Stock.census (Fin 3)
local notation "source₀" => WilsonThermometerCourseHearing.offered R A simple cut o
variable (P:WilsonOriginalReceivedChain.Post (N:=i+2) R hk D Q π Γ Ψ books ahead WilsonThermometerCourseHearing.disks sectors levels
  school.order school.horizon school.pieces i hi (WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_of_lt (Nat.lt_succ_self i)) o))

local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead WilsonThermometerCourseHearing.disks
  P.model school.order P.voter
local notation "lamps" => (rendered student (Ψ i).p (Coat.gStep (Ψ (i+1)).beta))
local notation "placed" => P.passport.coarser (R.family.path.levels.clock.op i per).ratio
local notation "n" => (school.order+school.horizon+2)
local notation "gf" => Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
local notation "stage" => R.alloy.B.a.clock.J i


open MeasureTheory
open private exponential from YM.Integration.WilsonFiniteProgramFieldBorel
local notation "tape" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "names₀" => WilsonThermometerCourseHearing.disks
variable (hearing:ℕ) (J:Voice G) (axes:Lattice.Order)
local notation "H₁" => radius R (invoice (Fintype.card (Fin 3)) (hearing+2*n)) 1 i
local notation "r₁" => amplitude R J (H₁) (i+2) per i
local notation "h₁" => (WilsonDegreeFourInheritedRange.height R (hearing+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1
local notation "τ₁" => angularCut (R.family.path.levels.clock.hatBeta i)
local notation "cold" => House.chilly (G:=G) (plaquettes (placed).origin (H₁)) (τ₁)
local notation "angle₁" => WilsonJointAxialHearing.angleOf (placed).origin (h₁) J axes (r₁) gf
local notation "link₁" z:max =>
  WilsonCapturedPrimaryPotential.potential gf ((r₁) • WilsonJointAxialWindow.direction (placed).origin (h₁) J axes (r₁) z)
local notation "who" x:max =>
  Air.craft student (fun v=>(student v).paint x) levels (π i) tape
local notation "intake" x:max => Air.craft P.model (fun v=>(P.model v).paint x) levels (π (i+1)) tape
local notation "step₁" => (RunFormalChain.fromRun R).step (i+2) i per cut
local notation "bank" x:max z:max => WilsonThermometerRegisteredAllFiled.numerical R A π Γ school o x z
local notation "panel₀" x:max z:max =>
  WilsonCoherentMayerWindingGrades.panel school.order (gf:ℂ) (fun d=>Air.discharge (who x) d z)


open WilsonThermometerCenteredAlgebra WilsonFiniteOrdinaryInverse Primitives.GCC.Anchor WilsonReceivedWholeFieldHot
open Multi Extra.Trajectories Comparison.RG02.Cumulants WilsonIndependentOrdinaryPairGrade Push.AbsoluteSums

local notation "finite₁" x:max F:max t:max U:max =>
  Order.value (gf:ℂ) (Order.ratio (Bulk.Fk (step₁) F t (intake x) (angle₁ U) school.order))

def issued (Q₀:Poly (faces)) (x:Wallet names₀)
    (F:Forest (R.family.path.levels.clock.op i per).ratio) (tag:(R.family.path.levels.clock.op i per).Choices)
    (U:Config G (R.family.side i per)) : ℂ :=
  ∑ s:(faces).Mode, weight Q₀ s*((Poly.pass (bare lamps x U)).part s-
    (cold).indicator (fun field=>(finite₁ x F tag field).part s) U)

def declared (Q₀:Poly (faces)) (x:Wallet names₀) (U:Config G (R.family.side i per)) : ℂ :=
  ∑ s:(faces).Mode,weight Q₀ s*((Poly.pass (bare lamps x U)).part s-
    (cold).indicator (fun field=>(bank x (link₁ field)).part s) U)

theorem split (Q₀:Poly (faces)) (x:Wallet names₀)
    (F:Forest (R.family.path.levels.clock.op i per).ratio) (tag:(R.family.path.levels.clock.op i per).Choices) :
    declared R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀ x =
      fun U=>issued R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀ x F tag U+
        WilsonThermometerRegisteredAllWeighted.centered R simple A hk D Q π Γ Ψ books hi ahead school o P
          hearing J axes Q₀ x F tag U := by
  funext U
  unfold declared issued WilsonThermometerRegisteredAllWeighted.centered
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  unfold WilsonThermometerRegisteredAllWeighted.difference
  by_cases hu:U∈cold <;> simp only [Set.indicator_of_mem,Set.indicator_of_notMem,hu,not_false_eq_true]
  all_goals ring

local notation "C₃" => WilsonFiniteOrdinaryInverse.fee (faces)
local notation "profit" p:max => WilsonReceivedCloseOrdinaryGrade.invoice (faces) 3 0 (p+160) 1
local notation "extras" p:max => (4:ℝ)^(p+161+2*n*3)*(Fintype.card (Multi.parts (faces)).Mode)*((2:ℝ)^n)^3
variable (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
  Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)

include course in
theorem envelope {η:ℝ} {T:Campaign R} {W:Campaign.Pillars R T} (funded:FundedOriginalProperties.{u} simple η W)
    (slow:∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (clear:Clear G J) {ε:ℝ} (ep:0<ε)
    (law:VowsR.LawScroll G φ) (enrolled:VowsR.Chamber law R.kit D Q books)
    (fund:Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (late:max (WilsonJointAxialRoster.opening R simple funded slow J clear (Fintype.card (Fin 3)) n hearing ep)
        (WilsonReceivedAxialFiling.opening R simple D φ width school.order school.horizon (Fintype.card (Fin 3)) ep) ≤ i)
    (finiteLate:max (WilsonReceivedAxialFinite.opening R simple hearing ep)
        (WilsonReceivedAxialFinite.massOpening R D levels school.order school.horizon school.pieces (k:=k) simple width) ≤ i)
    (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow:school.horizon ≤ stage) (load:P.op.count ≤ Burn.horizon k+2) (fit:k ≤ stage)
    (room:3 ≤ school.order+1) (Q₀:Poly (faces)) (x:Wallet names₀)
    (F:Forest (R.family.path.levels.clock.op i per).ratio) (tag:(R.family.path.levels.clock.op i per).Choices) :
    RG.Envelope (issued R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀ x F tag) := by
  let E:=ε*(regulatorRun R.family (i+2) per i)^hearing+ε*gf^school.order+ε*gf^hearing
  let Drow:=(Spill.allOver (Ψ i).p)^(school.order+school.horizon+1)*
    Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead school.order school.horizon
  let nominal (s:(faces).Mode) (U:Config G (R.family.side i per)) := (Poly.pass (bare lamps x U)).part s
  let actual (s:(faces).Mode) (U:Config G (R.family.side i per)) := (finite₁ x F tag U).part s
  let offset (s:(faces).Mode) (U:Config G (R.family.side i per)) := nominal s U-(cold).indicator (actual s) U
  let b (s:(faces).Mode):=max (charge s Drow/Poly.toll P.w s) (WilsonJointAxialHearing.feeFor s 0 gf E/Poly.toll P.w s)
  have Gs:=WilsonReceivedSourceGross.landed R hk D Q π Γ Ψ books hi ahead names₀ sectors levels
    school.order school.horizon school.pieces source₀ P
  letI : Countable P.modelIndex:=P.modelCount
  letI students : Countable (Scene.Texts P.model
    (Pane.panel R.alloy i (R.alloy.B.a.S.oneStep i per).exact_size).ratio
    (Cruise.publish D R.rolls Q R.alloy φ books P.op (Oak.era R hk D Q π Γ hi P.op P.lesson)
      (R.alloy.B.a.S.oneStep i per).exact_size P.model school.order P.voter P.lesson.entry)) := Scene.crewC P.model
    (Pane.panel R.alloy i (R.alloy.B.a.S.oneStep i per).exact_size).ratio
    (Cruise.publish D R.rolls Q R.alloy φ books P.op (Oak.era R hk D Q π Γ hi P.op P.lesson)
      (R.alloy.B.a.S.oneStep i per).exact_size P.model school.order P.voter P.lesson.entry)
    (Cruise.funded D R.rolls Q R.alloy φ books P.op (Oak.era R hk D Q π Γ hi P.op P.lesson)
      (R.alloy.B.a.S.oneStep i per).exact_size P.model school.order P.voter P.lesson.entry P.lesson.studied ahead)
  have support:0 ≤ (Ψ i).p.supportExponent+1+1 := by linarith only [(Ψ i).p.exponent_pos]
  have left (s) : Measurable (nominal s) := @WilsonReceivedWholeFieldHot.borel _ _ _ _ _ _ _ _ _ _
    lamps _ _ _ P.issued.earning.positive support Gs students x s
  have right (s) : Measurable (actual s) := (WilsonFiniteProgramFieldBorel.original (step₁) F tag (intake x) gf school.order s).comp
    (WilsonJointAxialHearing.measuredAngle (placed).origin (h₁) J clear axes (r₁) gf)
  have bound (s) (U):‖offset s U‖ ≤ b s := by
    by_cases hU:U∈cold
    · have rates:=WilsonJointAxialOrdinary.selected R hk D Q π Γ Ψ course books hi cut ahead
        names₀ sectors levels school.order school.horizon school.pieces source₀ P simple funded slow J clear axes
        hearing ep width law enrolled fund late finiteLate pass hospital narrow load fit U hU
      have card:s.val.card ≤ 3 := (Finset.card_le_univ s.val).trans_eq (Fintype.card_fin 3)
      apply LE.le.trans _ (le_max_right ..)
      apply (le_div_iff₀ (Poly.worth P.salary.positive s)).mpr
      rw [mul_comm]
      have bound₀:=rates.2.2.2.2.2 x F tag s 0 (by omega)
      simp only [offset,Set.indicator_of_mem hU,nominal,actual,E,WilsonJointAxialHearing.angleOf] at bound₀ ⊢
      exact bound₀
    · apply LE.le.trans _ (le_max_left ..)
      apply (le_div_iff₀ (Poly.worth P.salary.positive s)).mpr
      rw [mul_comm]
      simpa only [offset,Set.indicator_of_notMem hU,sub_zero] using
        WilsonReceivedWholeFieldHot.ordinary lamps P.issued.earning.positive support Gs x U s
  refine ⟨Finset.measurable_fun_sum _ (fun s _=>measurable_const.mul
    ((left s).sub ((right s).indicator (House.bath ..)))),∑s,‖weight Q₀ s‖*b s,?_⟩
  intro U
  calc
    _ ≤ ∑s,‖weight Q₀ s*offset s U‖:=norm_sum_le ..
    _ = ∑s,‖weight Q₀ s‖*‖offset s U‖:=by simp only [norm_mul]
    _ ≤ _:=Finset.sum_le_sum fun s _=>mul_le_mul_of_nonneg_left (bound s U) (norm_nonneg _)

/-- Integrate the actual signed sum before returning it to any previous Wilson date. -/
theorem combined {G:Gauge} (R:Run G) {i N per j:ℕ} (live:i ≤ N) (age:j ≤ i)
    (X Y:Config G (R.family.side i per) → ℂ) (hx:RG.Envelope X) (hy:Measurable Y)
    (BX BY:ℝ) (px:(∫ U,‖X U‖ ∂scene R.family.path N per i) ≤ BX) (py:∀ U,‖Y U‖ ≤ BY) :
    (∫ U,‖actualTransport R.family (N:=N) (fun V=>X V+Y V) age U‖ ∂scene R.family.path N per j) ≤ BX+BY := by
  let μ:=scene R.family.path N per i
  haveI : IsProbabilityMeasure μ := OPE.Therm.probability (H:=R.family.path) (p:=per) R.makes.wilson live
  obtain ⟨mx,C,c⟩:=hx
  have ix:Integrable X μ:=Integrable.of_bound mx.aestronglyMeasurable C (ae_of_all _ c)
  have iy:Integrable Y μ:=Integrable.of_bound hy.aestronglyMeasurable BY (ae_of_all _ py)
  have both:RG.Envelope (fun V=>X V+Y V):=⟨mx.add hy,C+BY,fun U=>(norm_add_le ..).trans (add_le_add (c U) (py U))⟩
  calc
    _ ≤ ∫ U, ‖X U+Y U‖ ∂μ := ActualWilsonAbsoluteTransport.first R.family R.makes live
      (ActualWilsonAbsoluteTransport.weighted R.family R.makes live both) age
    _ ≤ ∫ U, ‖X U‖+‖Y U‖ ∂μ := integral_mono (ix.add iy).norm (ix.norm.add iy.norm) (fun _=>norm_add_le ..)
    _ = (∫ U,‖X U‖ ∂μ)+(∫ U,‖Y U‖ ∂μ):=integral_add ix.norm iy.norm
    _ ≤ BX+(∫ _:Config G (R.family.side i per),BY ∂μ):=add_le_add px
      (integral_mono iy.norm (integrable_const BY) py)
    _ = _:=by rw [integral_const,probReal_univ,one_smul]

include course in
theorem on_post {η:ℝ} {T:Campaign R} {W:Campaign.Pillars R T}
    (funded:FundedOriginalProperties.{u} simple η W)
    (slow:∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (clear:Clear G J) {ε:ℝ} (ep:0<ε) (modest:ε≤1) (p:ℕ)
    (reserve:p+164 ≤ hearing) (room:hearing ≤ school.order)
    (law:VowsR.LawScroll G φ) (enrolled:VowsR.Chamber law R.kit D Q books)
    (fund:Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (late:max (WilsonJointAxialRoster.opening R simple funded slow J clear (Fintype.card (Fin 3)) n hearing ep)
        (WilsonReceivedAxialFiling.opening R simple D φ width school.order school.horizon (Fintype.card (Fin 3)) ep) ≤ i)
    (finiteLate:max (WilsonReceivedAxialFinite.opening R simple hearing ep)
        (WilsonReceivedAxialFinite.massOpening R D levels school.order school.horizon school.pieces (k:=k) simple width) ≤ i)
    (clockLate:(eventually_atTop.mp (WilsonJointAxialClock.original R simple)).choose ≤ i)
    (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fit:k ≤ stage) (visible:WilsonThermometerRegisteredAllStation.Visible R simple A hk D Q π Γ Ψ books
      school o ahead hi P hearing ε)
    (Q₀:Poly (faces)) (price:Poly.price (fun v=>gf*P.w v) (inverseMass Q₀) ≤ C₃)

    (fraction:ε*(3^hearing+2) ≤ 1) (gate:WilsonReportingForestAngularReflection.posted R)
    (rareLate:WilsonJointAxialScalar.opening (V:=Fin 3) R simple gate hearing n (p+161+2*n*3) ≤ i)
    (x:Wallet names₀) (F:Forest (R.family.path.levels.clock.op i per).ratio)
    (tag:(R.family.path.levels.clock.op i per).Choices) :
    let delta:=declared R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀ x
    let C₀:=C₃*((profit p)+(extras p))*gf^(p+1)
    let C₁:=C₃*(profit p)*gf^(p+1)
    RG.Envelope delta ∧ ∀ j (age:j ≤ i), (∫ U,‖actualTransport R.family (N:=i+2) delta age U‖
      ∂scene R.family.path (i+2) per j) ≤ C₀+C₁ := by
  intro delta C₀ C₁
  let X:=issued R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀ x F tag
  let Y:=WilsonThermometerRegisteredAllWeighted.centered R simple A hk D Q π Γ Ψ books hi ahead school o P
    hearing J axes Q₀ x F tag
  have eq:delta=fun V=>X V+Y V:=split R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀ x F tag
  have hx:=envelope R simple A hk D Q π Γ Ψ course books hi ahead school o P hearing J axes width funded
    slow clear ep law enrolled fund late finiteLate pass hospital visible.2.2.2.1 visible.2.2.1 fit (by omega) Q₀ x F tag
  have hy:=WilsonThermometerRegisteredAllWeighted.on_post R simple A hk D Q π Γ Ψ course books hi ahead school o P
    hearing J axes width funded slow clear ep modest p reserve room law enrolled fund late finiteLate clockLate pass hospital fit
    visible Q₀ price x F tag
  obtain ⟨gp,small,_,_⟩ := (eventually_atTop.mp (WilsonJointAxialClock.original R simple)).choose_spec i clockLate (i+2) per cut
  have restored:=WilsonThermometerCenteredWeight.original Q₀ P.w P.salary.positive gp small 157
    (visible.2.1 full) price
  have fromIssued:=WilsonJointAxialRefund.original R hk D Q π Γ Ψ course books hi cut ahead names₀ sectors levels
    school.order school.horizon school.pieces source₀ P simple funded slow J clear axes hearing ep width law enrolled fund
    late finiteLate pass hospital visible.2.2.2.1 visible.2.2.1 fit gate p 160
    (by simpa only [Fintype.card_fin] using reserve) room fraction clockLate rareLate x F tag univ (weight Q₀) C₃ restored i le_rfl
  have bx:(∫ U,‖X U‖ ∂scene R.family.path (i+2) per i) ≤ C₀:= by
    simp only [actualTransport_base R.family R.makes (cut).le,Fintype.card_fin,X,issued,C₀] at fromIssued ⊢
    exact fromIssued
  rw [eq]
  refine ⟨?_,fun j age=>combined R (cut).le age X Y hx hy.1 C₀ C₁ bx hy.2.1⟩
  obtain ⟨mx,b,hb⟩:=hx
  exact ⟨mx.add hy.1,b+C₁,fun U=>(norm_add_le ..).trans (add_le_add (hb U) (hy.2.1 U))⟩

end YM.Integration.WilsonThermometerRegisteredOlderMaterial
