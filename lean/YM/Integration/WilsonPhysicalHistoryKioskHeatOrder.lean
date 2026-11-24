import YM.Integration.WilsonPhysicalHistoryKioskHeat
import YM.RG01.Slack
import YM.Pert.Asymptotics.RawAxis

/-! The original recorded beta band and RG01 decay turn the local rough
integral into a uniform coupling-power price, including a detector that
costs a fixed inverse power of the physical coupling. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskHeatOrder
open Function Filter Set Finset Lattice Wilson RG WilsonStartup RG.Shoot OPE.Therm Push.AbsoluteSums.Animals
open MeasureTheory IterationFour PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Topology Classical BigOperators

variable {G : Gauge} (R : Run G) (simple : G.Simple) (temperatures : Poetry R.family.path.levels)
local notation "g" => regulatorRun R.family
local notation "κ" => R.family.path.levels.clock.forcedAllowance

include simple in
private theorem rent (d q : ℕ) {C ε : ℝ} (cn : 0≤C) (ep : 0<ε) :
    ∀ᶠ i : ℕ in atTop, ∀ N, i≤N → ∀ per,
      (C/(g N per i)^d)*(625*(Fintype.card PlaqAxes:ℝ))*(κ i) ≤ ε*(g N per i)^q := by
  let A := R.family.path.levels
  let D : ℝ := 625*(Fintype.card PlaqAxes:ℝ)
  have dn : 0≤D := by dsimp [D]; positivity
  let δ := ε/(C*D+1)
  have cd : 0<C*D+1 := by positivity
  have hp : 0<δ := div_pos ep cd
  have two : 0<(2:ℝ)^(d+q) := by positivity
  have small := (RG01.Physical.shrink simple A (d+q)).eventually_lt_const (div_pos hp two)
  filter_upwards [small] with i clock N dated per
  let β := (R.family.path.rep N per i).beta
  have record : R.family.path.Conv N per i := R.makes.wilson.represents N per i dated
  have hh : 1<A.clock.hatBeta i := A.fits.delayed i
  have band : β∈Set.Icc (A.clock.hatBeta i/2) (2*A.clock.hatBeta i) := record.band
  have bp : 0<β := (div_pos (zero_lt_one.trans hh) (by norm_num)).trans_le band.1
  have root : Real.sqrt β ≤ 2*A.clock.hatBeta i := by
    nlinarith [Real.sq_sqrt bp.le,sq_nonneg (Real.sqrt β-1),band.2]
  have gp : 0<g N per i := inv_pos.mpr (Real.sqrt_pos.mpr bp)
  have tail : κ i ≤ δ*(g N per i)^(d+q) := by
    change A.clock.forcedAllowance i ≤ δ*((Real.sqrt β)⁻¹)^(d+q)
    rw [inv_pow,←div_eq_mul_inv,le_div_iff₀ (pow_pos (Real.sqrt_pos.mpr bp) _)]
    calc
      _ ≤ A.clock.forcedAllowance i*(2*A.clock.hatBeta i)^(d+q) := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) root _) (Real.exp_nonneg _)
      _ = 2^(d+q)*(A.clock.hatBeta i^(d+q)*A.clock.forcedAllowance i) := by rw [mul_pow]; ring
      _ ≤ 2^(d+q)*(δ/2^(d+q)) := mul_le_mul_of_nonneg_left clock.le two.le
      _ = _ := mul_div_cancel₀ _ two.ne'
  have buy : C*D*δ ≤ ε :=
    (mul_le_mul_of_nonneg_right (by linarith : C*D≤C*D+1) hp.le).trans_eq (mul_div_cancel₀ _ cd.ne')
  calc
    _ ≤ (C/(g N per i)^d)*D*(δ*(g N per i)^(d+q)) :=
      mul_le_mul_of_nonneg_left tail (mul_nonneg (div_nonneg cn (pow_nonneg gp.le _)) dn)
    _ = (C*D*δ)*(g N per i)^q := by rw [pow_add]; field_simp [gp.ne']
    _ ≤ ε*(g N per i)^q := mul_le_mul_of_nonneg_right buy (pow_nonneg gp.le _)
include simple temperatures in
theorem spatial (f d q : ℕ) {C ε : ℝ} (cn : 0 ≤ C) (ep : 0 < ε) :
    ∀ᶠ i : ℕ in atTop, ∀ N, i≤N → ∀ per H (x : Site (R.family.side i per)),
      ∀ F J : Config G (R.family.side i per) → ℂ, Measurable F → Measurable J →
      (∀ U, Healthy (R.family.path.rep N per i).p.threshold (neighbors (H+H) x) U → F U=0) →
      ∀ u : ℝ, 0<u → (∀ U, ‖F U‖ * (ballCost H:ℝ) ≤ u) →
      (∀ U, ‖J U‖ ≤ C/(g N per i)^d) → ∀ j (hj : j ≤ i),
      ∫ V, ‖actualTransport R.family (N:=N) (p:=per)
        (fun U => ((Real.sqrt (κ i))^f)⁻¹ • (J U * F U)) hj V‖
        ∂scene R.family.path N per j ≤ u*(ε*(g N per i)^q) := by
  filter_upwards [WilsonPhysicalHistoryKioskHeat.measured R simple temperatures f,rent R simple d q cn ep]
    with i thermal paid N dated per H x F J fmeas jmeas healthy u up salary probe j hj
  let FF := fun U => (u:ℂ)⁻¹*F U
  let JJ := fun U => (u:ℂ)*J U
  have same (U) : JJ U*FF U=J U*F U := by
    dsimp [FF,JJ]
    field_simp [Complex.ofReal_ne_zero.mpr up.ne']
  have scal : ‖(u:ℂ)‖=u := by rw [Complex.norm_real,Real.norm_of_nonneg up.le]
  have charge (U) : ‖FF U‖*(ballCost H:ℝ) ≤ 1 := by
    dsimp only [FF]
    rw [norm_mul,norm_inv,scal,mul_assoc,←div_eq_inv_mul,div_le_one up]
    exact salary U
  have fee (U) : ‖JJ U‖ ≤ u*(C/(g N per i)^d) := by
    dsimp only [JJ]
    rw [norm_mul,scal]
    exact mul_le_mul_of_nonneg_left (probe U) up.le
  have actual := thermal N dated per H x FF JJ (measurable_const.mul fmeas)
    (measurable_const.mul jmeas) (fun U clean => by simp [FF,healthy U clean])
    charge _ fee j hj
  simp_rw [same] at actual
  calc
    _ ≤ (u*(C/(g N per i)^d))*(625*(Fintype.card PlaqAxes:ℝ))*(κ i) := actual
    _ = u*((C/(g N per i)^d)*(625*(Fintype.card PlaqAxes:ℝ))*(κ i)) := by ring
    _ ≤ u*(ε*(g N per i)^q) := mul_le_mul_of_nonneg_left (paid N dated per) up.le

include simple temperatures in
theorem paid (f d q : ℕ) {C ε : ℝ} (cn : 0 ≤ C) (ep : 0 < ε) :
    ∀ᶠ i : ℕ in atTop, ∀ N, i≤N → ∀ per H (x : Site (R.family.side i per)),
      ∀ F J : Config G (R.family.side i per) → ℂ, Measurable F → Measurable J →
      (∀ U, Healthy (R.family.path.rep N per i).p.threshold (neighbors (H+H) x) U → F U=0) →
      (∀ U, ‖F U‖ * (ballCost H:ℝ) ≤ 1) →
      (∀ U, ‖J U‖ ≤ C/(g N per i)^d) → ∀ j (hj : j ≤ i),
      ∫ V, ‖actualTransport R.family (N:=N) (p:=per)
        (fun U => ((Real.sqrt (κ i))^f)⁻¹ • (J U * F U)) hj V‖
        ∂scene R.family.path N per j ≤ ε*(g N per i)^q := by
  filter_upwards [spatial R simple temperatures f d q cn ep] with i bought N dated per H x F J
    mF mJ healthy cap probe j hj
  simpa only [one_mul] using bought N dated per H x F J mF mJ healthy 1 zero_lt_one cap probe j hj

end YM.Integration.WilsonPhysicalHistoryKioskHeatOrder
end
