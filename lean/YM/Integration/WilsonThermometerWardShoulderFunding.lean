import YM.Integration.WilsonThermometerWardSolvedShoulder
import YM.Integration.WilsonThermometerAncestralCalendar
import YM.Integration.WilsonReceivedCloseOrdinaryScale

/-! Finance the retained pupil's rent and its restored wage at the actual
upper thermal argument of the signed reading on the elected Wilson post. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerWardShoulderFunding
open Filter Finset Lattice Wilson RG QuadraticLocal QuadraticLocal.Advent PhysMS
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G)
local notation "hat" => R.alloy.B.a.clock.hatBeta
local notation "B" => budgetR R
private def stage (a q:ℕ)(η:ℝ) := 8*(2:ℝ)^a*η*3^(q+2*a+2)

private theorem cancel (a q:ℕ) (η g:ℝ) (gp:0<g):
    (8*(2*(g⁻¹)^2)^a)*(η*(3*g)^(q+2*a+2))=stage a q η*g^(q+2):=by
  rw [mul_pow,mul_pow,←pow_mul,inv_pow,show q+2*a+2=q+2+2*a by omega,
    pow_add g (q+2) (2*a)]
  unfold stage
  rw [show q+2*a+2=q+2+2*a by omega]
  field_simp

theorem original (simple:G.Simple) (a q loss:ℕ) {η:ℝ} (fee:0≤η):
    ∀ᶠ j:ℕ in atTop,∀N per,j<N→
    let x:=regulatorRun R.family N per j
    let g:=regulatorRun R.family N per (j+1)
    ∀(Ω e W A:ℝ)(s:ℕ),1≤Ω→Ω≤B j→s≤a→0≤e→e≤η*x^(q+2*a+2)→
    0≤W→x^loss*W≤A→
      (8*Ω^s)*e+(1/4)*g^q≤g^q ∧ g^loss*W≤3^loss*A:=by
  let gate:=(eventually_atTop.mp (RG01.Physical.nextHat simple R.alloy.B.a)).choose
  have small:=WilsonDyadicReportingPrice.reserve (C:=R.family) simple R.makes (stage a q η) 0 (1/4)
    (by unfold stage; positivity) (by norm_num)
  filter_upwards [eventually_ge_atTop gate,WilsonThermometerAncestralCalendar.weak R simple,
    WilsonReceivedCloseChainFunding.upper R simple 0 0,(tendsto_add_atTop_nat 1).eventually small]
    with j calendar weak forward allow
  intro N per live x g Ω e W A s op beta digits ep incurred wp salary
  have newborn:=weak N per (j+1) (Nat.le_succ j) live
  have parent:=weak N per j le_rfl live.le
  have gp:0<g:=newborn.1
  have xp:0<x:=parent.1
  have smallFee:stage a q η*g≤1/4:=by simpa using allow per N live
  have up:g≤3*x:=(forward j le_rfl (by simp [PaceR.Close]) N per live.le (j+1) (Nat.le_succ j) live).2
  have inverse:g⁻¹≤3*x⁻¹:=WilsonReceivedCloseOrdinaryScale.inverse R simple (i:=j) (b:=j)
    le_rfl live calendar
  have down:x≤3*g:=by
    rw [←one_div,←div_eq_mul_inv] at inverse
    have z:=(div_le_div_iff₀ gp xp).mp inverse
    simpa [mul_comm] using z
  let β:=R.family.path.β N per (j+1)
  have low:hat (j+1)/2≤β:=(R.makes.wilson.represents N per (j+1) live).band.1
  have actual:(g⁻¹)^2=β:=by
    change (((Real.sqrt β)⁻¹)⁻¹)^2=β
    rw [inv_inv,Real.sq_sqrt (by linarith only [low,R.alloy.B.a.fits.delayed (j+1)])]
  have head:Ω≤2*(g⁻¹)^2:=by
    rw [actual]
    exact (beta.trans (WilsonOriginalThermometerTollBudget.parameter R j)).trans (by linarith only [low])
  have cash:(8*Ω^s)*e≤ stage a q η*g^(q+2):=by
    apply le_trans _ (cancel _ _ _ _ gp).le
    refine mul_le_mul (mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ op digits).trans
      (pow_le_pow_left₀ (zero_le_one.trans op) head _)) (by norm_num)) ?_ ep (by positivity)
    exact incurred.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ xp.le down _) fee)
  constructor
  · have bound:stage a q η*g^(q+2)≤(1/4)*g^q:=by
      calc stage a q η*g^(q+2) = (stage a q η*g)*g^(q+1):=by rw [pow_succ g (q+1)];ring
           _ ≤ (1/4)*g^q:=mul_le_mul smallFee (pow_le_pow_of_le_one gp.le newborn.2 (by omega))
             (pow_nonneg gp.le _) (by norm_num)
    linarith only [cash,bound,pow_nonneg gp.le q]
  · calc g^loss*W≤(3*x)^loss*W:=mul_le_mul_of_nonneg_right
           (pow_le_pow_left₀ gp.le up loss) wp
         _=3^loss*(x^loss*W):=by rw [mul_pow,mul_assoc]
         _≤3^loss*A:=mul_le_mul_of_nonneg_left salary (by positivity)

end YM.Integration.WilsonThermometerWardShoulderFunding
