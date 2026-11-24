import YM.Integration.WilsonThermometerRegisteredAllMaterial
import YM.Integration.WilsonThermometerRegisteredAllFiled
import YM.Integration.WilsonThermometerRegisteredAllPrice
import YM.Integration.WilsonThermometerEarlierHearing
import YM.Integration.WilsonFiniteProgramFieldBorel
import YM.Integration.WilsonJointAxialHearing

/-! All ordinary faces of the independently declared numerical program on the genuine
two-date Wilson chart, tested against the original marginal at every older date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredAllCold

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
variable (p:ℕ) (J:Voice G) (axes:Lattice.Order)
local notation "H₁" => radius R (invoice (Fintype.card (Fin 3)) ((p+161)+2*n)) 1 i
local notation "r₁" => amplitude R J (H₁) (i+2) per i
local notation "h₁" => (WilsonDegreeFourInheritedRange.height R ((p+161)+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1
local notation "τ₁" => angularCut (R.family.path.levels.clock.hatBeta i)
local notation "cold" => House.chilly (G:=G) (plaquettes (placed).origin (H₁)) (τ₁)
local notation "angle₁" => WilsonJointAxialHearing.angleOf (placed).origin (h₁) J axes (r₁) gf
local notation "link₁" z:max =>
  WilsonCapturedPrimaryPotential.potential gf ((r₁) • WilsonJointAxialWindow.direction (placed).origin (h₁) J axes (r₁) z)
local notation "budget" => WilsonThermometerRegisteredAllPrice.fee*gf^(p+1)
local notation "who" x:max =>
  Air.craft student (fun v=>(student v).paint x) levels (π i) tape
local notation "intake" x:max => Air.craft P.model (fun v=>(P.model v).paint x) levels (π (i+1)) tape
local notation "step₁" => (RunFormalChain.fromRun R).step (i+2) i per cut
local notation "bank" x:max z:max => WilsonThermometerRegisteredAllFiled.numerical R A π Γ school o x z
local notation "panel₀" x:max z:max =>
  WilsonCoherentMayerWindingGrades.panel school.order (gf:ℂ) (fun d=>Air.discharge (who x) d z)

def difference (x:Wallet names₀) (F:Forest (R.family.path.levels.clock.op i per).ratio)
    (tag:(R.family.path.levels.clock.op i per).Choices) (s:(faces).Mode) :
    Config G (R.family.side i per) → ℂ :=
  (cold).indicator (fun U=>
    (Order.value (gf:ℂ) (Order.ratio (Bulk.Fk (step₁) F tag (intake x) (angle₁ U) school.order))).part s -
      (bank x (link₁ U)).part s)

variable (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
  (degree:p+160 ≤ school.order)

include course degree in
/-- The named filed comparison on the funded lower post. `filed` is the conclusion of
`RegisteredAllFiled.on_trail` on the actual appointed trail and its numbered upper pupil. -/
theorem on_post {η:ℝ} {T:Campaign R} {W:Campaign.Pillars R T}
    (funded:FundedOriginalProperties.{u} simple η W)
    (slow:∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (clear:Clear G J)
    (law:VowsR.LawScroll G φ) (enrolled:VowsR.Chamber law R.kit D Q books)
    (fund:Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (late:max (WilsonJointAxialRoster.opening R simple funded slow J clear (Fintype.card (Fin 3)) n (p+161) zero_lt_one)
        (WilsonReceivedAxialFiling.opening R simple D φ width school.order school.horizon (Fintype.card (Fin 3)) zero_lt_one) ≤ i)
    (finiteLate:max (WilsonReceivedAxialFinite.opening R simple (p+161) zero_lt_one)
        (WilsonReceivedAxialFinite.massOpening R D levels school.order school.horizon school.pieces (k:=k) simple width) ≤ i)
    (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow:school.horizon ≤ stage) (load:P.op.count ≤ Burn.horizon k+2) (fit:k ≤ stage)
    (roof:∀ s:(faces).Mode, gf^157 ≤ Poly.toll P.w s)
    (filed:∀ (x:Wallet names₀) (z:Stationary.Link G (R.family.side i per)),
      bank x z = Poly.pass (panel₀ x (Stationary.arm G (R.family.side i per) 1 z)))
    (x:Wallet names₀) (F:Forest (R.family.path.levels.clock.op i per).ratio)
    (tag:(R.family.path.levels.clock.op i per).Choices) (s:(faces).Mode) :
    let error:=difference R simple A hk D Q π Γ Ψ books hi ahead school o P p J axes x F tag s
    Measurable error ∧ (∀ U, ‖error U‖ ≤ budget) ∧
      WilsonThermometerCompulsoryReturn.Heard R (top:=i+2) error (budget) := by
  intro error
  have gp : 0 < gf := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  have letter (t:(faces).Mode) : Measurable (fun U=>(panel₀ x (angle₁ U)).part t) :=
    (WilsonThermometerRegisteredTrace.panel (who x) school.order (gf:ℂ) t).measurable.comp
      (WilsonJointAxialHearing.measuredAngle (placed).origin (h₁) J clear axes (r₁) gf)
  have receipt : Measurable (fun U=>(bank x (link₁ U)).part s) := by
    simp only [filed]
    exact exponential letter s
  have left:Measurable (fun U=>(Order.value (gf:ℂ) (Order.ratio
      (Bulk.Fk (step₁) F tag (intake x) (angle₁ U) school.order))).part s) :=
    (WilsonFiniteProgramFieldBorel.original (step₁) F tag (intake x) gf school.order s).comp
      (WilsonJointAxialHearing.measuredAngle (placed).origin (h₁) J clear axes (r₁) gf)
  have borel:Measurable error:=(left.sub receipt).indicator (House.bath ..)
  have bound (U): ‖error U‖ ≤ budget := by
    by_cases hU:U∈cold
    · change ‖(cold).indicator _ U‖ ≤ _
      rw [Set.indicator_of_mem hU]
      rw [filed,norm_sub_rev]
      have here:=WilsonThermometerRegisteredAllMaterial.original R simple A hk D Q π Γ Ψ course books hi ahead
        school.order school.horizon school.pieces o P width (p+161) funded slow J clear axes zero_lt_one
        law enrolled fund late finiteLate pass hospital narrow load fit U hU x F tag s (p+158)
        (by have sz : s.val.card ≤ 3 := (Finset.card_le_univ s.val).trans_eq (Fintype.card_fin 3);omega)
      obtain ⟨_,r0,r1,cap,_,_⟩:=WilsonJointAxialFolded.selected R hk D Q π Γ Ψ course books hi cut ahead
        names₀ sectors levels school.order school.horizon school.pieces source₀ P simple funded slow J clear
        axes (p+161) zero_lt_one width late pass hospital narrow load fit U hU
      have small:=(WilsonReceivedAxialFinite.priced R hk D Q π Γ Ψ course books hi cut ahead
        names₀ sectors levels school.order school.horizon school.pieces source₀ P simple width law enrolled fund
        (p+161) zero_lt_one finiteLate fit _ cap r0 r1).1
      exact WilsonThermometerRegisteredAllPrice.paid p s gp small (roof s) (by simpa only [WilsonJointAxialHearing.angleOf,one_mul] using here)
    · change ‖(cold).indicator _ U‖ ≤ _
      rw [Set.indicator_of_notMem hU,norm_zero]
      unfold WilsonThermometerRegisteredAllPrice.fee
      positivity
  exact ⟨borel,bound,WilsonThermometerEarlierHearing.original R (Nat.le_add_right i 2) borel bound⟩

end YM.Integration.WilsonThermometerRegisteredAllCold
