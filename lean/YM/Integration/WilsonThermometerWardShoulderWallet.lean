import YM.Integration.WilsonThermometerWardShoulderAperture
import YM.Integration.WilsonReceivedCloseReentry

/-! The three-slot natural wage restored over the actual booked close interval. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerWardShoulderWallet
open Filter Finset Lattice Wilson RG Source Labels QuadraticLocal QuadraticLocal.Advent AllOrder PhysMS
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open Pressure Push.PriceCompiler AllOrder.Floe.Step
open WilsonOriginalStarSceneRent WilsonOriginalThermometerPalette WilsonThermometerCourseHearing
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G)
local notation "hat" => R.alloy.B.a.clock.hatBeta
local notation "budget" => budgetR R
local notation "marks" => Stock.census (Fin 3)
local notation "cash" => max 1 (wallet R levels 0)
local notation "term" K:max b:max => ((1+K)*cash*(hat (b+1))^3)

theorem birth (D:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (φ:ℕ→ℕ)(paid:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (b k:ℕ)(available:k≤R.alloy.B.a.clock.J (b+1))
    (width:WilsonOriginalThermometerTollBudget.reach R≤R.alloy.B.a.clock.J (b+1)+1)
    (Ω K:ℝ)(op:0≤Ω)(feasible:Ω≤budget b)(non:0≤K):
    max 1 ((1+K)*wallet R levels (Poetry.Agenda.seed D φ k (R.alloy.B.a.clock.J (b+1))))*Ω≤term K b:=by
  have wage:=WilsonOriginalThermometerTollBudget.income R D φ paid (b+1) k available width
  have one:1≤hat (b+1):=(R.alloy.B.a.fits.delayed (b+1)).le
  have positive:1≤(1+K)*cash*(hat (b+1))^2:=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (le_max_left ..))
      (one_le_pow₀ one)
  have real: (1+K)*wallet R levels (Poetry.Agenda.seed D φ k (R.alloy.B.a.clock.J (b+1)))≤
      (1+K)*cash*(hat (b+1))^2:= by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left ((wage).trans
      (mul_le_mul_of_nonneg_right (le_max_right ..) (sq_nonneg _))) (by linarith)
  exact (mul_le_mul (max_le positive real) (feasible.trans (WilsonOriginalThermometerTollBudget.parameter R b))
    op (zero_le_one.trans positive)).trans_eq (by ring)

theorem stamps (simple:G.Simple) (degree:ℕ) {cap δ:ℝ} (base:0≤cap) (small:0<δ):
    ∀ᶠ b:ℕ in atTop,∀m≤b,PaceR.Close R degree cap m b→∀N per,b≤N→∀j,m≤j→j≤b→
    ∀h:ℝ,0≤h→h≤∏l∈Ico j b,(budget l)^2*(budget (l+1))^7→
      h^3≤(regulatorRun R.family N per b)^(-δ):=by
  filter_upwards [WilsonReceivedCloseReentry.envelope R simple degree 3 base small] with b buy
  intro m mb close N per live j mj jb h hp receipt
  have stamps:=buy m mb close N per live j mj jb
  let tariff:=∏l∈Ico j b,(budget l)^(2*3)*(budget (l+1))^(7*3)
  have cost:(∏l∈Ico j b,(budget l)^2*(budget (l+1))^7)^3=tariff:=by
    simp only [tariff,←Finset.prod_pow,mul_pow,←pow_mul]
  have positive:0≤tariff:=by
    apply prod_nonneg
    intro l _
    exact mul_nonneg (pow_nonneg (zero_le_one.trans (budget_pos R)) _)
      (pow_nonneg (zero_le_one.trans (budget_pos R)) _)
  exact ((pow_le_pow_left₀ hp receipt 3).trans_eq cost).trans ((le_mul_of_one_le_right positive
    (PaceR.roof_ge (R:=R) (i:=j) (b:=b))).trans stamps)

theorem original (simple:G.Simple) (degree:ℕ) {cap δ:ℝ} (base:0≤cap) (small:0<δ):
    ∀ᶠ b:ℕ in atTop,∀m≤b,PaceR.Close R degree cap m b→∀per j,m≤j→j≤b→
    ∀(D:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (φ:ℕ→ℕ)(_paid:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (k:ℕ)(_available:k≤R.alloy.B.a.clock.J (b+1))
    (_width:WilsonOriginalThermometerTollBudget.reach R≤R.alloy.B.a.clock.J (b+1)+1)
    (Ω K h:ℝ),1≤Ω→Ω≤budget b→0≤K→1≤h→h≤∏l∈Ico j b,(budget l)^2*(budget (l+1))^7→
    let A:=max 1 ((1+K)*wallet R levels (Poetry.Agenda.seed D φ k (R.alloy.B.a.clock.J (b+1))))*Ω
    ∀(w:Fin 3→ℝ)(c:(marks).Mode→ℂ),WilsonGeometricSignedCapture.weightBill c w=(∑s,‖c s‖*(A*h)^s.val.card)→
      WilsonGeometricSignedCapture.weightBill c w ≤ (∑s,‖c s‖)*(term K b)^3*
        (regulatorRun R.family (b+1) per b)^(-δ):=by
  filter_upwards [stamps R simple degree base small] with b quote
  intro m mb close per j mj jb D φ paid k available width Ω K h og feasible kp hp limit A w c bill
  have born:A≤term K b:=birth R D φ paid b k available width Ω K (zero_le_one.trans og) feasible kp
  have ap:1≤A:=one_le_mul_of_one_le_of_one_le (le_max_left ..) og
  have price:h^3≤(regulatorRun R.family (b+1) per b)^(-δ):=
    quote m mb close (b+1) per b.le_succ j mj jb h (zero_le_one.trans hp) limit
  calc
    _≤(∑s,‖c s‖)*((term K b)^3*(regulatorRun R.family (b+1) per b)^(-δ)):=by
      rw [bill,Finset.sum_mul]
      apply Finset.sum_le_sum
      intro s _
      have count:s.val.card≤3:=by simpa using (Finset.card_le_univ s.val)
      have all:1≤A*h:=one_le_mul_of_one_le_of_one_le ap hp
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      refine (pow_le_pow_right₀ all count).trans ?_
      rw [mul_pow]
      exact mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans ap) born _) price
        (pow_nonneg (zero_le_one.trans hp) _) (pow_nonneg ((zero_le_one.trans ap).trans born) _)
    _=_:=(mul_assoc ..).symm


end YM.Integration.WilsonThermometerWardShoulderWallet
