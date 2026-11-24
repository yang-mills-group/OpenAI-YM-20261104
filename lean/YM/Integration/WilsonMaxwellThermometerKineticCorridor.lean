import YM.Integration.ActualRunBetaResetDomain
import YM.Integration.WilsonMaxwellThermometerKineticRunning

/-! The true Wilson kinetic readings at two finite dates of the same original course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerKineticCorridor
open Filter RG Lattice Wilson PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Topology Classical
variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.β
local notation "𝛃" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a
local notation "g" => regulatorRun R.family

include simple in
theorem beta (m k N per : ℕ) (mk : m≤k) (before : k≤N) :
    |β N per m-β N per k| ≤ (G.slopeConstant+1)*(Real.log (a m)-Real.log (a k)) := by
  induction k,mk using Nat.le_induction with
  | base => simp
  | succ j _ prior =>
    have old:=prior ((Nat.le_succ j).trans before)
    have live:=Nat.lt_of_lt_of_le (Nat.lt_succ_self j) before
    have next:=ActualRunBetaResetDomain.adjacent_step_bound R simple N per j live
    change |β N per j-β N per (j+1)|≤(G.slopeConstant+1)*Real.log ((R.family.S.block j).val:ℝ) at next
    apply (abs_sub_le (β N per m) (β N per j) (β N per (j+1))).trans ((add_le_add old next).trans_eq ?_)
    have hp : (0:ℝ)<(R.family.S.block j).val := by exact_mod_cast (R.family.S.block j).property
    rw [R.family.S.a_step,Real.log_div (R.family.S.a_pos j).ne' hp.ne']
    ring

include simple in
theorem original (m k N per : ℕ) (mk : m≤k) (before : k≤N) :
    |g N per k / g N per m - 1| ≤
      2*(G.slopeConstant+1)*(Real.log (a m)-Real.log (a k))/𝛃 m := by
  let x:=Real.sqrt (β N per m)
  let y:=Real.sqrt (β N per k)
  have bm:=Overlay.beta_positive R.makes.wilson (mk.trans before) (p:=per)
  have bk:=Overlay.beta_positive R.makes.wilson before (p:=per)
  have xp : 0<x := Real.sqrt_pos.mpr bm
  have yp : 0<y := Real.sqrt_pos.mpr bk
  have xx : x^2=β N per m := Real.sq_sqrt bm.le
  have yy : y^2=β N per k := Real.sq_sqrt bk.le
  have hm : 0<𝛃 m := zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have hk : 0<𝛃 k := zero_lt_one.trans (R.family.path.levels.fits.delayed k)
  have mono : 𝛃 m≤𝛃 k := (Real.log_le_log_iff hm hk).mp (WilsonAdmissionScale.logarithm_monotone A simple mk)
  have band : 𝛃 k/2 ≤ β N per k := (R.makes.wilson.represents N per k before).band.1
  let t:=x/y-1
  have factor : |t| *((x+y)*y)=|β N per m-β N per k| := by
    rw [←abs_of_nonneg (show 0≤(x+y)*y by positivity),←abs_mul]
    congr 1
    dsimp [t]
    field_simp [yp.ne']
    nlinarith [xx,yy]
  have ll : 𝛃 m/2 ≤ (x+y)*y := by nlinarith [mul_nonneg xp.le yp.le,yy]
  have spent := ((mul_le_mul_of_nonneg_left ll (abs_nonneg t)).trans_eq factor).trans
    (beta R simple m k N per mk before)
  change |y⁻¹/x⁻¹-1| ≤ _
  rw [show y⁻¹/x⁻¹=x/y by field_simp [xp.ne',yp.ne']]
  change |t|≤_
  apply (le_div_iff₀ hm).mpr
  linarith

end YM.Integration.WilsonMaxwellThermometerKineticCorridor
