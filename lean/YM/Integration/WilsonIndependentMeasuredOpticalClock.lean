import YM.Integration.WilsonPositionProgramTrialOpticalBand

/-! The genuine Wilson heat on the registered planting mesh. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMeasuredOpticalClock
open Filter Lattice RG Source Labels PhysicalNext.Repeat.Legato
open WilsonPositionProgramTrialOpticalBand (Band Bracket)
open WilsonInvariantActionPosition (berth)
variable {G : Gauge} (R : Run G) (good : G.Simple) (V : XSpace.Run)
local notation "H" => R.family.path.levels.clock.hatBeta

include good in
theorem heat {m K i : ℕ} (mesh : R.family.S.a K/R.family.S.a m=(V.step i).spacing)
    (invoice : 2+Real.log (H m) ≤ Real.log (R.family.S.a m/R.family.S.a K)) :
    H m ≤ (V.den i : ℝ) ∧ H K ≤ (1+G.slopeConstant)*(V.den i : ℝ) := by
  have den : 0 < (V.den i : ℝ) := by exact_mod_cast V.den_pos i
  have a : 0 < H m := zero_lt_one.trans (R.family.path.levels.fits.delayed m)
  have ratio : R.family.S.a m/R.family.S.a K=(V.den i : ℝ) := by
    rw [← inv_div,mesh]
    change ((V.den i : ℝ)⁻¹)⁻¹=_
    rw [inv_inv]
  rw [ratio] at invoice
  have low := (Real.log_le_log_iff a den).mp (by linarith only [invoice] : Real.log (H m) ≤ Real.log (V.den i))
  have span : R.family.S.scale K - R.family.S.scale m=Real.log (V.den i) := by
    rw [←ratio,Real.log_div (R.family.S.a_pos m).ne' (R.family.S.a_pos K).ne']
    unfold Schedule.scale
    rw [Real.log_inv,Real.log_inv]
    ring
  have exactHeat : H K=H m+G.slopeConstant*Real.log (V.den i) := by
    rw [←span]
    change (_+G.slopeConstant*R.family.S.scale K)=(_+G.slopeConstant*R.family.S.scale m)+_
    ring
  have spent := mul_le_mul_of_nonneg_left (Real.log_le_self den.le) (Gauge.slopeConstant_pos good).le
  rw [exactHeat]
  exact ⟨low,by linarith only [spent,low]⟩

include good in
theorem original {K : ℕ → ℕ} {stage : ℕ} (B : Band R V K stage) {A : ℝ} (paid : Bracket R K A) :
    ∀ᶠ t : ℕ in atTop,
      let m:=B.reporter+t
      H m ≤ (V.den (B.mesh t) : ℝ) ∧ H (K m) ≤ (1+G.slopeConstant)*(V.den (B.mesh t) : ℝ) := by
  have later : Tendsto (fun t:ℕ => B.reporter+t) atTop atTop :=
    tendsto_atTop_mono (fun n=>Nat.le_add_left n _) tendsto_id
  filter_upwards [later.eventually paid] with n grant
  exact heat R good V (B.spacing n) grant.2.1

end YM.Integration.WilsonIndependentMeasuredOpticalClock
