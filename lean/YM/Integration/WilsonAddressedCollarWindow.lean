import YM.Integration.WilsonAddressedCollarSlates
import YM.Integration.WilsonInvariantActionPosition

/-! Both sides of the physical first-mesh estimate. The one-block overshoot is
    subpower at the reporter before selecting either regulator. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedCollarWindow
open Filter Real Lattice Wilson RG Source Extra.Histories RG05Readout RG05Readout.Address
open RG05Readout.Planes WilsonLimitConstruction Next.Rank Trace.Pilot PhysicalNext.Repeat.Legato Bandage
open WilsonInvariantActionPosition
open private finer from YM.Integration.WilsonInvariantActionPosition
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "α" => R.family.S.a
local notation "s" => R.family.S.scale

private theorem distance (m u : ℕ) : s u-s m = log (α m/α u) := by
  rw [Schedule.scale,Schedule.scale,log_inv,log_inv,log_div
    (R.family.S.a_pos m).ne' (R.family.S.a_pos u).ne']
  ring

include simple in
private theorem delay (c : ℝ) {η : ℝ} (hp : 0 < η) :
    ∀ᶠ m : ℕ in atTop, 2 + log c + log (β m) ≤ (β m)^η := by
  have b := Station.hat_rate R.family.path.levels simple
  have tail := b.eventually ((isLittleO_log_rpow_atTop hp).bound (c:=1/2) (by norm_num))
  have cash := (tendsto_rpow_atTop hp).comp b
  filter_upwards [tail,cash.eventually_ge_atTop (2*(2+log c))] with m h k
  have bp := zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have logbill : log (β m) ≤ (1/2:ℝ)*(β m)^η :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,abs_of_nonneg (rpow_nonneg bp.le η)]
      using h)
  change 2*(2+log c) ≤ (β m)^η at k
  linarith

include slow simple in
theorem original (t : ℕ) {η : ℝ} (positive : 0 < η) :
    ∀ᶠ m : ℕ in atTop, let u := berth R t m
      m < u ∧ (β m)^t ≤ α m/α u ∧ α m/α u ≤ (β m)^t * (β m)^η := by
  let c : ℝ := 1+G.slopeConstant*t
  have slope := Gauge.slopeConstant_pos simple
  have cpos : 0 < c := lt_of_lt_of_le zero_lt_one
    (le_add_of_nonneg_right (mul_nonneg slope.le (Nat.cast_nonneg _)))
  filter_upwards [delay R simple c positive] with m margin
  let u := berth R t m
  have gate := arrival R t m
  have bp := zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have attained : (β m)^t ≤ α m / α u := (le_div_iff₀ (R.family.S.a_pos u)).mpr
    (by simpa only [mul_comm] using gate.2)
  refine ⟨gate.1,attained,?_⟩
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (n:=u) (by have := gate.1; omega)
  have mj : m ≤ j := by have h : m < u := gate.1; omega
  have jm : α m / α j ≤ (β m)^t := by
    by_cases same : m = j
    · rw [←same,div_self (R.family.S.a_pos m).ne']
      exact one_le_pow₀ (R.family.path.levels.fits.delayed m).le
    · by_contra! exceeds
      have before : j < berth R t m := by change j < u; omega
      exact Nat.find_min (finer R m t) before
        ⟨lt_of_le_of_ne mj same,(by
          simpa only [mul_comm] using ((lt_div_iff₀ (R.family.S.a_pos j)).mp exceeds).le)⟩
  have ratio := log_le_log (div_pos (R.family.S.a_pos m) (R.family.S.a_pos j)) jm
  rw [log_pow,←distance R m j] at ratio
  have budget : β j ≤ c * β m := by
    have age : β j - β m = G.slopeConstant*(s j - s m) := by
      change (_+G.slopeConstant*s j)-(_+G.slopeConstant*s m)=_;ring
    have earlier := mul_le_mul_of_nonneg_left ratio slope.le
    have unit := mul_le_mul_of_nonneg_left (log_le_self bp.le)
      (mul_nonneg slope.le (Nat.cast_nonneg t))
    dsimp only [c]; nlinarith only [age,earlier,unit]
  have small : ((R.family.S.block j).val : ℝ) ≤ (β m)^η := by
    have bj := zero_lt_one.trans (R.family.path.levels.fits.delayed j)
    have hlog := log_le_log bj budget
    rw [log_mul cpos.ne' bp.ne'] at hlog
    have later := slow.2 j
    have qpos : 0 ≤ 2+log (β j) := by
      have := log_nonneg (R.family.path.levels.fits.delayed j).le; linarith
    change _ ≤ log (2 + log (β j)) at later
    exact later.trans ((log_le_self qpos).trans ((by linarith only [hlog,margin])))
  change α m / α u ≤ _
  rw [hj,R.family.S.a_step]
  calc
    _ = α m / α j * ((R.family.S.block j).val : ℝ) := by field_simp
    _ ≤ _ := mul_le_mul jm small (Nat.cast_nonneg _) (pow_nonneg bp.le _)

end YM.Integration.WilsonAddressedCollarWindow
