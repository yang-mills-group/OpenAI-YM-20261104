import YM.Integration.WilsonOriginalThermometerReportedGrading
import YM.Integration.WilsonOriginalThermometerTollBudget

/-! The extra inverse transfer from the nominated reporting age has a fixed source price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalThermometerReportedToll
open Finset Lattice Wilson RG Source Labels QuadraticLocal Earn Sunrise AllOrder AllOrder.Floe.Step
open Pressure Push.PriceCompiler PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonOriginalThermometerPalette WilsonOriginalThermometerMicroscopic WilsonOriginalStarSceneWords WilsonOriginalStarSceneRent
open WilsonOriginalThermometerTollBudget
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "A₀" => R.alloy.B.a
local notation "Y" n:max => R.alloy.B.a.clock.hatBeta n

include simple in
private theorem rising (m:ℕ) : Y m ≤ Y (m+1):=by
  rw [beta_eq R.alloy.B.valid m]
  exact le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos simple).le
    (Real.log_nonneg (Nat.one_le_cast.mpr (R.rolls.L _).property)))

include simple in
theorem coordinate (i:ℕ) :
    WilsonOriginalThermometerReportedGrading.cap R i 1 ≤ (Y (i+2))^7*WilsonOriginalThermometerTopGrading.cap R (i+1) 1 := by
  let y:=Y (i+2)
  have y0:0 ≤ y:=zero_le_one.trans ((A₀).fits.delayed (i+2)).le
  have m0:0 ≤ mass R:=sum_nonneg fun _ _=>mul_nonneg (by unfold WilsonPositionThermometerStationNorm.cost; positivity) (by positivity)
  have b0:0 ≤ Y (i+1):=zero_le_one.trans ((A₀).fits.delayed (i+1)).le
  simp only [WilsonOriginalThermometerReportedGrading.cap,WilsonOriginalThermometerTopGrading.cap,Real.rpow_one]
  exact mul_le_mul_of_nonneg_left 
    (mul_le_mul (pow_le_pow_left₀ b0 (rising R simple (i+1)) 7) 
      (mul_le_mul_of_nonneg_right (rising R simple i) m0) (mul_nonneg (zero_le_one.trans ((A₀).fits.delayed i).le) m0)
      (pow_nonneg y0 _)) (pow_nonneg y0 _)

include simple in
theorem original (D:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (φ:ℕ→ℕ) (paid:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (i k:ℕ) (available:k ≤ (A₀).clock.J (i+2)) (width:reach R ≤ (A₀).clock.J (i+2)+1)
    {Ω:ℝ} (op:0 ≤ Ω) (feasible:Ω ≤ Advent.budgetR R (i+1)) :
    max 1 ((1+WilsonOriginalThermometerReportedGrading.cap R i 1)*
      wallet R levels (Poetry.Agenda.seed D φ k ((A₀).clock.J (i+2))))*Ω ≤ rate R*(Y (i+2))^18 := by
  let σ:=Poetry.Agenda.seed D φ k ((A₀).clock.J (i+2))
  let y:=Y (i+2)
  let c:=WilsonOriginalThermometerTopGrading.cap R (i+1) 1
  let d:=WilsonOriginalThermometerReportedGrading.cap R i 1
  let w:=wallet R levels σ
  let E:=max 1 ((1+c)*w)
  have h:1 ≤ y^7:=one_le_pow₀ ((A₀).fits.delayed (i+2)).le
  have z:0 ≤ y^7:=zero_le_one.trans h
  have pos:0 ≤ w:=sum_nonneg fun a _=>mul_nonneg (add_nonneg zero_le_one (mul_nonneg (positive ..).le
      (by cases a <;> simp [stencil]))) (Real.exp_nonneg _)
  have cc:1+d ≤ y^7*(1+c):=(add_le_add h (coordinate R simple i)).trans_eq (by ring)
  have x: max 1 ((1+d)*w) ≤ y^7*E :=
    max_le (one_le_mul_of_one_le_of_one_le h (le_max_left _ _))
      ((mul_le_mul_of_nonneg_right cc pos).trans ((mul_assoc ..).le.trans
        (mul_le_mul_of_nonneg_left (le_max_right _ _) z)))
  have cost:E*Ω ≤ rate R*y^11:=WilsonOriginalThermometerTollBudget.original R simple D φ paid (i+1) k available width op feasible
  exact (mul_le_mul_of_nonneg_right x op).trans
    ((mul_assoc ..).le.trans ((mul_le_mul_of_nonneg_left cost z).trans_eq (by ring)))

end YM.Integration.WilsonOriginalThermometerReportedToll
