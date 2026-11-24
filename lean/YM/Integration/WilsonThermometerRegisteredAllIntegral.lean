import YM.Integration.WilsonThermometerRegisteredAllCold
import YM.Integration.WilsonThermometerRegisteredIntegral
import YM.Integration.WilsonThermometerRegisteredAllStation

/-! Integrate all signed faces of the same two-date physical chart against the exact
relative-cell mass of the compact thermometer. The coefficients may vary from site to site. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredAllIntegral

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

/-- All phases use the same real relative-cell measure, with no volume factor. -/
theorem compact (Z:T₀ × T₀ → Config G (R.family.side i per)→ℂ) (B:ℝ) (ok:0≤B)
    (bounded:∀ y,Measurable (Z y) ∧ ∀ U, ‖Z y U‖≤B) (r:ℝ) (test:Test 3) :
    WilsonThermometerCompulsoryReturn.Heard R (top:=i+2)
      (fun U=>∑ y:T₀×T₀,WilsonThermometerAlignedCells.mass (R:=R) r (N₀) test y*Z y U)
      ((∫x:Points 3,‖test x‖)*B) := by
  let w:=WilsonThermometerAlignedCells.mass (R:=R) r (N₀) test
  apply WilsonThermometerEarlierHearing.original R (Nat.le_add_right i 2)
    (Finset.measurable_fun_sum _ fun y _=>measurable_const.mul (bounded y).1)
  intro U
  calc
    _ ≤ ∑ y:T₀×T₀,‖w y*Z y U‖:=norm_sum_le ..
    _ = ∑ y:T₀×T₀,‖w y‖*‖Z y U‖:=by simp only [norm_mul]
    _ ≤ ∑ y:T₀×T₀,‖w y‖*B:=Finset.sum_le_sum fun y _=>
      mul_le_mul_of_nonneg_left ((bounded y).2 U) (norm_nonneg _)
    _ = (∑y:T₀×T₀,‖w y‖)*B:=by rw [Finset.sum_mul]
    _ ≤ _:=mul_le_mul_of_nonneg_right (WilsonThermometerAlignedCells.variation (R:=R) r (N₀) test) ok

include course in
theorem on_filings
    (posts:∀ y:T₀×T₀,WilsonThermometerRegisteredIntegral.Post R simple A hk D Q π Γ Ψ books school ahead hi y)
    (p:ℕ) (J:Voice G) (axes:Lattice.Order) (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
    (degree:p+160 ≤ school.order)
    {η:ℝ} {T:Campaign R} {W:Campaign.Pillars R T} (funded:FundedOriginalProperties.{u} simple η W)
    (slow:∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (clear:Clear G J)
    (law:VowsR.LawScroll G φ) (enrolled:VowsR.Chamber law R.kit D Q books)
    (fund:Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (late:max (WilsonJointAxialRoster.opening R simple funded slow J clear (Fintype.card (Fin 3)) (rawSize) (p+161) zero_lt_one)
        (WilsonReceivedAxialFiling.opening R simple D φ width school.order school.horizon (Fintype.card (Fin 3)) zero_lt_one) ≤ i)
    (finiteLate:max (WilsonReceivedAxialFinite.opening R simple (p+161) zero_lt_one)
        (WilsonReceivedAxialFinite.massOpening R D levels school.order school.horizon school.pieces (k:=k) simple width) ≤ i)
    (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)

    (fit:k ≤ stage) (rentOrder:ℕ) (ε:ℝ)
    (certificate:∀ y:T₀×T₀,WilsonThermometerRegisteredAllStation.Visible R simple A hk D Q π Γ Ψ books
      school (placement (R:=R) (N₀) y) ahead hi (posts y) rentOrder ε)
    (x:T₀×T₀ → Wallet WilsonThermometerCourseHearing.disks)
    (F:T₀×T₀ → Forest (R.family.path.levels.clock.op i per).ratio)
    (tag:T₀×T₀ → (R.family.path.levels.clock.op i per).Choices)
    (c:T₀×T₀→(J₀).Mode→ℂ) (M:ℝ) (total:∀ y,∑ s,‖c y s‖ ≤ M)
    (r:ℝ) (test:Test 3) :
    let e (y:T₀×T₀) (s:(J₀).Mode):=WilsonThermometerRegisteredAllCold.difference R simple A hk D Q π Γ Ψ
      books hi ahead school (placement (R:=R) (N₀) y) (posts y) p J axes (x y) (F y) (tag y) s
    let B:=WilsonThermometerRegisteredAllPrice.fee*gf^(p+1)
    WilsonThermometerCompulsoryReturn.Heard R (top:=i+2)
      (fun U=>∑ y:T₀×T₀,WilsonThermometerAlignedCells.mass (R:=R) r (N₀) test y*∑ s,c y s*e y s U)
      ((∫z:Points 3,‖test z‖)*(M*B)) := by
  intro e B
  have slot (y:T₀×T₀) (s:(J₀).Mode) : Measurable (e y s) ∧ ∀ U, ‖e y s U‖ ≤ B := by
    obtain ⟨_,roof,load,narrow,filed⟩:=certificate y
    have result:=WilsonThermometerRegisteredAllCold.on_post R simple A hk D Q π Γ Ψ course books hi ahead
      school (placement (R:=R) (N₀) y) (posts y) p J axes width degree funded slow clear law enrolled fund late finiteLate
      pass hospital narrow load fit roof filed (x y) (F y) (tag y) s
    exact ⟨result.1,result.2.1⟩
  have bp:0≤B:=mul_nonneg (by unfold WilsonThermometerRegisteredAllPrice.fee;positivity)
    (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
  have mp:0≤M:=(Finset.sum_nonneg (fun s _=>norm_nonneg (c (0,0) s))).trans (total (0,0))
  refine compact R _ (M*B) (mul_nonneg mp bp) ?_ r test
  intro y
  refine ⟨Finset.measurable_fun_sum _ (fun s _=>measurable_const.mul (slot y s).1),?_⟩
  intro U
  calc
    _ ≤ ∑ s,‖c y s*e y s U‖:=norm_sum_le ..
    _ = ∑ s,‖c y s‖*‖e y s U‖:=by simp only [norm_mul]
    _ ≤ ∑ s,‖c y s‖*B:=Finset.sum_le_sum fun s _=>
      mul_le_mul_of_nonneg_left ((slot y s).2 U) (norm_nonneg _)
    _ = (∑s,‖c y s‖)*B:=by rw [Finset.sum_mul]
    _ ≤ _:=mul_le_mul_of_nonneg_right (total y) bp

end YM.Integration.WilsonThermometerRegisteredAllIntegral
