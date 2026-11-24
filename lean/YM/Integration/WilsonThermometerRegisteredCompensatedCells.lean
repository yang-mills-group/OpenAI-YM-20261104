import YM.Integration.WilsonThermometerRegisteredAllIntegral
import YM.Integration.WilsonThermometerRegisteredAllWeighted
import YM.Integration.WilsonThermometerCenteredMaterial
import YM.Integration.WilsonThermometerCenteredCompensation

/-! At each genuine pair of child offsets, issue the complete finite-material inverse on
that appointed post before integrating over the older Wilson field. The fixed probe and its
inverse may vary with the pair. Use a single radius restoration on their complete signed sum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredCompensatedCells

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

open WilsonThermometerRegisteredCells WilsonThermometerRegisteredIntegral WilsonThermometerAlignedCells
open MeasureTheory OPE OPE.Orbits XSpace.Rose Push.GridApprox
variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m i per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m (i+2) per k Ψ)
  {φ:ℕ → ℕ} (books:Mentor.Offices.Books D R.rolls Q φ) (hi:m ≤ i)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (school:Syl.School k)

local notation "T₀" => Site (R.family.side (i+2) per)
local notation "N₀" => ((i+2,per):RG12.UVIndex)
local notation "gf" => Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
local notation "J₀" => Stock.census (Fin 3)
local notation "rawSize" => (school.order+school.horizon+2)
local notation "stage" => R.alloy.B.a.clock.J i


open WilsonThermometerCenteredAlgebra WilsonFiniteOrdinaryInverse Primitives.GCC.Anchor Exterior
local notation "cut" => (Nat.lt_succ_of_lt (Nat.lt_succ_self i))
local notation "C₃" => WilsonFiniteOrdinaryInverse.fee (J₀)
local notation "actor" => WilsonThermometerCourseHearing.disks
local notation "tape" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "strip" => (∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
  Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
local notation "op₁" => R.family.path.levels.clock.op i per
local notation "program" => (RunFormalChain.fromRun R).step (i+2) i per cut
local notation "roster" P:max => Air.craft (P).model (fun v=>((P).model v).paint WilsonThermometerCourseHearing.fired) WilsonOriginalThermometerPalette.levels (π (i+1)) tape
local notation "base" => Stationary.arm G (R.family.side i per) 1
local notation "budget₁" => R.family.path.levels.budget i
local notation "β₁" => R.family.path.levels.clock.hatBeta i

def fixed (y:T₀ × T₀) (L:WilsonThermometerRegisteredIntegral.Post R simple A hk D Q π Γ Ψ books school ahead hi y) (a:Stationary.Link G (R.family.side i per)) : Poly (J₀) :=
  let W:=Air.craft L.model (fun v=>(L.model v).paint WilsonThermometerCourseHearing.fired)
    WilsonOriginalThermometerPalette.levels (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
  Order.value (gf:ℂ) (Order.ratio (PhysicalWilsonPeriodizedMaterial.reference R (i+2) i per cut
    (Stationary.arm G (R.family.side i per) 1 a) W school.order))

include course in
theorem income (y:T₀ × T₀) (L:WilsonThermometerRegisteredIntegral.Post R simple A hk D Q π Γ Ψ books school ahead hi y)
    (width:strip) (depth:ℕ) (H cap:ℝ) (hc:0 ≤ cap) (ready:(eventually_atTop.mp (WilsonThermometerCenteredCompensation.original R simple D φ width
      school.order school.horizon k school.pieces depth H cap hc)).choose ≤ i) (law:VowsR.LawScroll G φ)
    (enrolled:VowsR.Chamber law R.kit D Q books) (fund:Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (fit:k ≤ stage) (a:Stationary.Link G (R.family.side i per)) (z:ℝ)
    (rent:|z|≤|H| * (Real.log (β₁))^depth*(((budget₁).B:ℝ)^2*(budget₁).threshold)/gf)
    (inside:∀ e,‖Exterior.collect G ((base) a) e‖≤cap * |z|) :
    let table:=fixed R simple A hk D Q π Γ Ψ books hi ahead school y L a
    (∀ (F:Forest (op₁).ratio) (t:(op₁).Choices),
      Order.value (gf:ℂ) (Order.ratio (Bulk.Fk program F t (roster L) ((base) a) school.order))=table) ∧
      Poly.price (fun v=>gf*L.w v) (inverseMass table) ≤ C₃ := by
  intro table
  have same (F:Forest (op₁).ratio) (t:(op₁).Choices) := WilsonThermometerCenteredMaterial.posted R A simple
    hk D Q π Γ Ψ books hi cut ahead school.order school.horizon school.pieces (placement (R:=R) (N₀) y) L ((base) a) F t
  have value (F:Forest (op₁).ratio) (t:(op₁).Choices) :
      Order.value (gf:ℂ) (Order.ratio (Bulk.Fk program F t (roster L) ((base) a) school.order))=table :=
    congrArg (fun W=>Order.value (gf:ℂ) (Order.ratio W)) (same F t)
  let F₀:=WilsonCoeffUV.repeatF (op₁)
  let t₀:=PhysicalWilsonPeriodizedProgram.branch (op₁)
  have purchased:=(eventually_atTop.mp (WilsonThermometerCenteredCompensation.original R simple D φ width
    school.order school.horizon k school.pieces depth H cap hc)).choose_spec i ready
    A hk fit Q π Γ Ψ course books law enrolled fund hi cut (placement (R:=R) (N₀) y) ahead L a z rent inside F₀ t₀
  exact ⟨value,(value F₀ t₀) ▸ purchased.1⟩

include course in
theorem on_filings (width:strip) (depth:ℕ) (H cap:ℝ) (hc:0 ≤ cap)
    (posts:∀ y:T₀×T₀,WilsonThermometerRegisteredIntegral.Post R simple A hk D Q π Γ Ψ books school ahead hi y)
    (hearing:ℕ) (J:Voice G) (axes:Lattice.Order)
    {η:ℝ} {T:Campaign R} {W:Campaign.Pillars R T} (funded:FundedOriginalProperties.{u} simple η W)
    (slow:∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (clear:Clear G J) {ε:ℝ} (ep:0<ε) (modest:ε≤1) (p:ℕ)
    (reserve:p+164 ≤ hearing) (room:hearing ≤ school.order)
    (law:VowsR.LawScroll G φ) (enrolled:VowsR.Chamber law R.kit D Q books)
    (fund:Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (late:max (WilsonJointAxialRoster.opening R simple funded slow J clear (Fintype.card (Fin 3)) rawSize hearing ep)
        (WilsonReceivedAxialFiling.opening R simple D φ width school.order school.horizon (Fintype.card (Fin 3)) ep) ≤ i)
    (finiteLate:max (WilsonReceivedAxialFinite.opening R simple hearing ep)
        (WilsonReceivedAxialFinite.massOpening R D levels school.order school.horizon school.pieces (k:=k) simple width) ≤ i)
    (clockLate:(eventually_atTop.mp (WilsonJointAxialClock.original R simple)).choose ≤ i)
    (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fit:k ≤ stage) 

    (cert:∀ y:T₀×T₀, WilsonThermometerRegisteredAllStation.Visible R simple A hk D Q π Γ Ψ books
      school (placement (R:=R) (N₀) y) ahead hi (posts y) hearing ε)
    (ready:(eventually_atTop.mp (WilsonThermometerCenteredCompensation.original R simple D φ width
      school.order school.horizon k school.pieces depth H cap hc)).choose ≤ i) (a:T₀×T₀ → Stationary.Link G (R.family.side i per)) (z:T₀×T₀→ℝ)
    (rent:∀ y,|z y|≤|H| * (Real.log (β₁))^depth*(((budget₁).B:ℝ)^2*(budget₁).threshold)/gf)
    (inside:∀ y e,‖Exterior.collect G ((base) (a y)) e‖≤cap * |z y|)
    (F:T₀×T₀ → Forest (op₁).ratio) (tag:T₀×T₀ → (op₁).Choices) (r:ℝ) (test:Test 3) :
    let table:=fun y=>fixed R simple A hk D Q π Γ Ψ books hi ahead school y (posts y) (a y)
    let e:=fun y=>WilsonThermometerRegisteredAllWeighted.centered R simple A hk D Q π Γ Ψ books hi ahead school
      (placement (R:=R) (N₀) y) (posts y) hearing J axes (table y) fired (F y) (tag y)
    let cash:=C₃*WilsonReceivedCloseOrdinaryGrade.invoice (J₀) 3 0 (p+160) 1*gf^(p+1)
    WilsonThermometerCompulsoryReturn.Heard R (top:=i+2)
      (fun U=>∑ y:T₀×T₀,WilsonThermometerAlignedCells.mass (R:=R) r (N₀) test y*e y U)
      ((∫z:Points 3,‖test z‖)*cash) := by
  intro table e cash
  have roomNN:0 ≤ WilsonFiniteOrdinaryInverse.room (J₀) := Finset.sum_nonneg
    (fun s _=>mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have feeNN:0 ≤ C₃ := Finset.sum_nonneg (fun n _=>pow_nonneg (add_nonneg zero_le_one roomNN) n)
  have gNN:0≤gf:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have okay:0≤cash:=mul_nonneg (mul_nonneg feeNN
    (WilsonReceivedCloseOrdinaryGrade.nonneg (J₀) 3 0 (p+160) zero_le_one)) (pow_nonneg gNN _)
  refine WilsonThermometerRegisteredAllIntegral.compact R e cash okay ?_ r test
  intro y
  have fixedFee:=income R simple A hk D Q π Γ Ψ course books hi ahead school y (posts y)
    width depth H cap hc ready law enrolled fund fit (a y) (z y) (rent y) (inside y)
  have billed:=WilsonThermometerRegisteredAllWeighted.on_post R simple A hk D Q π Γ Ψ course books hi ahead school
    (placement (R:=R) (N₀) y) (posts y) hearing J axes width funded slow clear ep modest p reserve room
    law enrolled fund late finiteLate clockLate pass hospital fit (cert y) (table y) fixedFee.2 fired (F y) (tag y)
  exact ⟨billed.1,billed.2.1⟩

end YM.Integration.WilsonThermometerRegisteredCompensatedCells
