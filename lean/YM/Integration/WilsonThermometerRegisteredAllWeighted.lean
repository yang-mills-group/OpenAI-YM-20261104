import YM.Integration.WilsonThermometerRegisteredAllCold
import YM.Integration.WilsonThermometerRegisteredAllStation
import YM.Integration.WilsonJointAxialCash
import YM.Integration.WilsonJointAxialClock
import YM.Integration.WilsonThermometerCenteredWeight

/-! One restoration for the prescribed inverse and the ordinary masks together. The azimuth,
hearing order, measured field and held inverse are shared with the older physical comparison. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredAllWeighted

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

def difference (x:Wallet names₀) (F:Forest (R.family.path.levels.clock.op i per).ratio)
    (tag:(R.family.path.levels.clock.op i per).Choices) (s:(faces).Mode) :
    Config G (R.family.side i per) → ℂ :=
  (cold).indicator (fun U=>
    (Order.value (gf:ℂ) (Order.ratio (Bulk.Fk (step₁) F tag (intake x) (angle₁ U) school.order))).part s -
      (bank x (link₁ U)).part s)


open WilsonThermometerCenteredAlgebra WilsonFiniteOrdinaryInverse Primitives.GCC.Anchor
open private fee from YM.Integration.WilsonJointAxialCash

def centered (Q₀:Poly (faces)) (x:Wallet names₀) (F:Forest (R.family.path.levels.clock.op i per).ratio)
    (tag:(R.family.path.levels.clock.op i per).Choices) (U:Config G (R.family.side i per)) : ℂ :=
  ∑ s: (faces).Mode, weight Q₀ s*
    difference R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes x F tag s U

local notation "C₃" => WilsonFiniteOrdinaryInverse.fee (faces)
variable (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
  Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)

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
    (x:Wallet names₀) (F:Forest (R.family.path.levels.clock.op i per).ratio)
    (tag:(R.family.path.levels.clock.op i per).Choices) :
    let C₀:=WilsonReceivedCloseOrdinaryGrade.invoice (faces) 3 0 (p+160) 1
    let f:=centered R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀ x F tag
    Measurable f ∧ (∀ U,‖f U‖≤C₃*C₀*gf^(p+1)) ∧
      WilsonThermometerCompulsoryReturn.Heard R (top:=i+2) f (C₃*C₀*gf^(p+1)) := by
  intro C₀ f
  obtain ⟨clockPos,clockSmall,_,_⟩:=(eventually_atTop.mp (WilsonJointAxialClock.original R simple)).choose_spec i
    clockLate (i+2) per cut
  have gp : 0 < gf := clockPos
  have small : gf ≤ 1 := clockSmall
  let cell (s:(faces).Mode):=difference R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes x F tag s
  have borel (s:(faces).Mode) : Measurable (cell s) := by
    have letter (t:(faces).Mode):Measurable (fun U=>(panel₀ x (angle₁ U)).part t) :=
      (WilsonThermometerRegisteredTrace.panel (who x) school.order (gf:ℂ) t).measurable.comp
        (WilsonJointAxialHearing.measuredAngle (placed).origin (h₁) J clear axes (r₁) gf)
    have numeric:Measurable (fun U=>(bank x (link₁ U)).part s) := by
      simp only [visible.2.2.2.2]
      exact exponential letter s
    exact (((WilsonFiniteProgramFieldBorel.original (step₁) F tag (intake x) gf school.order s).comp
      (WilsonJointAxialHearing.measuredAngle (placed).origin (h₁) J clear axes (r₁) gf)).sub numeric).indicator
      (House.bath ..)
  have bankNN : 0 ≤ C₀ := WilsonReceivedCloseOrdinaryGrade.nonneg (faces) 3 0 (p+160) zero_le_one
  have credit := WilsonThermometerCenteredWeight.original Q₀ P.w P.salary.positive gp small 157
    (visible.2.1 full) price
  have perFace (s:(faces).Mode) (U:Config G (R.family.side i per)) :
      Poly.toll P.w s*‖cell s U‖ ≤ C₀*gf^(p+160+1) := by
    by_cases hU:U∈cold
    · change Poly.toll P.w s*‖(cold).indicator _ U‖ ≤ _
      rw [Set.indicator_of_mem hU,visible.2.2.2.2,norm_sub_rev]
      have card : s.val.card ≤ 3 := (Finset.card_le_univ s.val).trans_eq (Fintype.card_fin 3)
      have paid:=WilsonThermometerRegisteredAllMaterial.original R simple A hk D Q π Γ Ψ course books hi ahead
        school.order school.horizon school.pieces o P width hearing funded slow J clear axes ep
        law enrolled fund late finiteLate pass hospital visible.2.2.2.1 visible.2.2.1 fit U hU x F tag s
        (p+160+1) (by omega)
      have input : ε*gf^hearing ≤ gf^(p+160+1+3) :=
        (mul_le_of_le_one_left (pow_nonneg gp.le _) modest).trans
          (pow_le_pow_of_le_one gp.le small (by omega))
      have bill : WilsonThermometerRegisteredWindow.bill s gf (ε*gf^hearing) (p+160+1) ≤ C₀*gf^(p+160+1) :=
        fee (faces) s gp small 3 (p+160) card (mul_nonneg ep.le (pow_nonneg gp.le _)) input
      apply LE.le.trans _ bill
      simp only [WilsonJointAxialHearing.angleOf] at paid ⊢
      exact paid
    · change Poly.toll P.w s*‖(cold).indicator _ U‖ ≤ _
      rw [Set.indicator_of_notMem hU,norm_zero,mul_zero]
      exact mul_nonneg bankNN (pow_nonneg gp.le _)
  have measured:Measurable f := Finset.measurable_fun_sum _ fun s _=>measurable_const.mul (borel s)
  have bound (U):‖f U‖ ≤ C₃*C₀*gf^(p+1) := by
    have swapped (s) : ‖cell s U‖ ≤ (C₀*gf^(p+160+1))/Poly.toll P.w s :=
      (le_div_iff₀ (show 0<Poly.toll P.w s from Finset.prod_pos (fun v _=>P.salary.positive v))).mpr (by
        rw [mul_comm (‖cell s U‖)]; exact perFace s U)
    calc
      ‖f U‖ ≤ ∑ s, ‖weight Q₀ s*cell s U‖ := norm_sum_le ..
      _ = ∑ s, ‖weight Q₀ s‖*‖cell s U‖:=by simp only [norm_mul]
      _ ≤ ∑ s, (‖weight Q₀ s‖/Poly.toll P.w s)*(C₀*gf^(p+160+1)):=by
        apply Finset.sum_le_sum
        intro s _
        calc
          _ ≤ ‖weight Q₀ s‖*((C₀*gf^(p+160+1))/Poly.toll P.w s):=
            mul_le_mul_of_nonneg_left (swapped s) (norm_nonneg _)
          _ = _:=by ring
      _ = (gf^160*∑ s,‖weight Q₀ s‖/Poly.toll P.w s)*C₀*gf^(p+1) := by
        rw [←Finset.sum_mul,show p+160+1=160+(p+1) by omega,pow_add];ring
      _ ≤ _:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right credit bankNN) (pow_nonneg gp.le _)
  exact ⟨measured,bound,WilsonThermometerEarlierHearing.original R (Nat.le_add_right i 2) measured bound⟩

end YM.Integration.WilsonThermometerRegisteredAllWeighted
