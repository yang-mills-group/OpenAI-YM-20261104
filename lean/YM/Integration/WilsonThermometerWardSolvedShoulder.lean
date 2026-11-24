import YM.Integration.WilsonThermometerWardShoulderPower

/-! The actual microscopic three-coordinate wage and the corresponding
restored finite face price for an enrolled corrected (6,4,4) source. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerWardSolvedShoulder
open Function Filter Finset Lattice Wilson RG Source Labels QuadraticLocal QuadraticLocal.Advent AllOrder PhysMS
open RG05Readout RG05Readout.Address PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open Pressure Push.PriceCompiler AllOrder.Floe.Step WilsonOriginalStarSceneRent WilsonOriginalThermometerPalette
open WilsonCapturedPrimaryActiveArms WilsonCapturedPrimaryWardGapAperture WilsonThermometerOwnOffsetField
open WilsonThermometerOffsetTrajectory WilsonPositionThermometerCapStation
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G)
local notation "fam" => R.family
local notation "budget" => budgetR R
local notation "marks" => Stock.census (Fin 3)
local notation "cash" => max 1 (wallet R levels 0)

def coin {N p:ℕ} (E:(i:Fin 3)→(fam).label (levels i)) (i:Fin 3):ℝ:=
  ((fam).labels.level (levels i)).coeffSize (Next.Rank.Price.awake (fam) (levels i) N N p (E i))

theorem original (simple:G.Simple) (degree:ℕ) {cap:ℝ} (base:0≤cap):
    ∀ᶠ k₀:ℕ in atTop,∀ᶠ b:ℕ in atTop,∀m≤b,PaceR.Close R degree cap m b→∀per j,m≤j→j≤b→
    let x:=regulatorRun (fam) (b+1) per j
    x≤1→∀(o:Fin 3→Site ((fam).side (b+1) per))(S:Shelf (N:=b+1) (p:=per) R k₀ levels o)
    (live:k₀≤b+1)(_ref:∀i,(fam).ref (levels i)≤b+1)(y:(i:Fin 3)→Palette (fam) (levels i))(T:ℕ),
    (fam).S.scale (b+1)-(fam).S.scale k₀≤T*Real.log x⁻¹→
    let E:=exposed R levels o S live y
    let K:=∑i,coin R (N:=b+1) (p:=per) E i
    let Y:=∑i,size (y i)
    (0≤K ∧ ∀i,coin R (N:=b+1) (p:=per) E i≤K) ∧
    K≤(x⁻¹)^(7*T)*Y ∧
    ∀(D:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (φ:ℕ→ℕ)(_paid:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (k:ℕ)(_available:k≤R.alloy.B.a.clock.J (b+1))
    (_width:WilsonOriginalThermometerTollBudget.reach R≤R.alloy.B.a.clock.J (b+1)+1)
    (Ω h:ℝ),1≤Ω→Ω≤budget b→1≤h→h≤∏l∈Ico j b,(budget l)^2*(budget (l+1))^7→
    let A:=max 1 ((1+K)*wallet R levels (Poetry.Agenda.seed D φ k (R.alloy.B.a.clock.J (b+1))))*Ω
    ∀(w:Fin 3→ℝ)(c:(marks).Mode→ℂ),WilsonGeometricSignedCapture.weightBill c w=(∑s,‖c s‖*(A*h)^s.val.card)→
    x^(21*T+19)*WilsonGeometricSignedCapture.weightBill c w≤(∑s,‖c s‖)*(((1+Y)*cash*36^3)^3*3):=by
  filter_upwards [WilsonThermometerWardShoulderAperture.original R] with k₀ income
  filter_upwards [WilsonThermometerWardShoulderPower.original R simple degree base,
    WilsonReceivedCloseChainFunding.upper R simple degree cap] with b invoice real
  intro m mb close per j mj jb x small o S live ref y T span E K Y
  have xpos:0<x:=(real m mb close (b+1) per b.le_succ j mj (jb.trans b.le_succ)).1
  have xone:1≤x⁻¹:=(one_le_inv₀ xpos).mpr small
  have unit (i:Fin 3):0≤coin R (N:=b+1) (p:=per) E i:=Work.G08.size_nonneg .. 
  have paid:0≤K:=Finset.sum_nonneg fun i _=>unit i
  have cost:K≤(x⁻¹)^(7*T)*Y:=by
    dsimp only [K,Y]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have target:levels i+1≤7:=by fin_cases i <;> decide
    have power:T*(levels i+1)≤7*T:=(Nat.mul_le_mul_left T target).trans_eq (Nat.mul_comm ..)
    exact (income levels o S live ref y x xpos T span i).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ xone power) (size_ge _))
  refine ⟨⟨paid,fun i=>Finset.single_le_sum (f:=fun l=>coin R (N:=b+1) (p:=per) E l)
    (fun l _=>unit l) (Finset.mem_univ i)⟩,cost,?_⟩
  intro D φ grant k available width Ω h one eligible positive limit A w c wage
  exact invoice m mb close per j mj jb small D φ grant k available width Ω K h Y T one eligible paid positive
    limit (Finset.sum_nonneg fun i _=>size_ge (y i)) cost w c wage

end YM.Integration.WilsonThermometerWardSolvedShoulder
