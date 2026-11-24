import YM.Integration.WilsonOriginalThermometerReportedToll
import YM.Integration.WilsonOriginalThermometerTollBudget
import YM.Integration.WilsonReceivedClosePhysicalBirths

/-! The inverse-tuned three-field source two dates above its original measurement. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseReportedWallet
open Filter Lattice Wilson RG QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent AllOrder AllOrder.Floe AllOrder.Floe.Step
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonOriginalThermometerPalette WilsonOriginalThermometerMicroscopic WilsonOriginalStarSceneWords
open WilsonPositionThermometerGradedSource WilsonOriginalStarSceneRent
open WilsonOriginalThermometerTopGrading WilsonOriginalThermometerTollBudget
open scoped BigOperators Classical

variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "A₀" => R.alloy.B.a
local notation "g" n:max j:max p:max => regulatorRun R.family n p j

def unit := rate R*4^18

theorem covers : 1 ≤ unit R := one_le_mul_of_one_le_of_one_le (le_max_left ..) (by norm_num)

theorem sold (D:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (φ:ℕ→ℕ) (fund:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (i k N per:ℕ) (top:i+1 ≤ N) (available:k ≤ (A₀).clock.J (i+2))
    (width:reach R ≤ (A₀).clock.J (i+2)+1)
    (calendar:(eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose ≤ i+1)
    {Ω:ℝ} (pos:0 ≤ Ω) (paid:Ω ≤ budgetR R (i+1)) :
    let σ:=Poetry.Agenda.seed D φ k ((A₀).clock.J (i+2))
    let E:=max 1 ((1+WilsonOriginalThermometerReportedGrading.cap R i 1)*wallet R levels σ)
    E*Ω ≤ unit R*((g N (i+1) per)⁻¹)^36 := by
  intro σ E
  have fee:=WilsonOriginalThermometerReportedToll.original R simple D φ fund i k available width pos paid
  have next:=(eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose_spec (i+1) calendar
  let y:=R.family.path.β N per (i+1)
  have init:=(R.makes.wilson.represents N per (i+1) top).band.1
  change (A₀).clock.hatBeta (i+1)/2 ≤ y at init
  have hot:=(R.alloy.B.a.fits.delayed (i+1))
  have y0:0 ≤ y:=by linarith only [hot,init]
  have adj:(A₀).clock.hatBeta (i+2) ≤ 4*y := by linarith only [next,init]
  have sign:0 ≤ rate R:=zero_le_one.trans (le_max_left ..)
  calc
    E*Ω ≤ rate R*((A₀).clock.hatBeta (i+2))^18 := fee
    _ ≤ rate R*(4*y)^18 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀
       (zero_le_one.trans ((A₀).fits.delayed (i+2)).le) adj _) sign
    _ = unit R*((g N (i+1) per)⁻¹)^36 := by
      change _=unit R*((Real.sqrt y)⁻¹⁻¹)^36
      rw [inv_inv,show 36=2*18 by decide,pow_mul,Real.sq_sqrt y0,mul_pow,unit]
      ring

end YM.Integration.WilsonReceivedCloseReportedWallet
