import YM.Integration.WilsonReceivedCloseEndpoint

/-! The true upper curvature appointment enters below every requested close comparison order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseCalibratedBudget
open Filter RG Wilson QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Mentor Extra.Histories
open Pert.Asymptotics PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato

variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "H" => R.alloy.B.a.clock.hatBeta
local notation "B" => budgetR R

include simple in
theorem original (q : ℕ) {κ : ℝ} (kp : 0<κ) :
    ∀ᶠ j:ℕ in atTop, ∀ N per, j ≤ N → ∀ order, q+2 ≤ order →
      8*B (j+1)*(H ((j+1)+1))^(-(order:ℝ)) ≤ κ*(3*regulatorRun R.family N per j)^q := by
  have grow := RG01.Physical.hats simple R.alloy.B.a
  filter_upwards [grow.eventually_ge_atTop (max 2 (8/κ))] with j heat N per jN order covered
  let u := H ((j+1)+1)
  let y := R.family.path.β N per j
  have rise : H j ≤ u := WilsonStartup.Timing.hat_mono R.alloy.B.a (Gauge.slopeConstant_pos simple).le (by omega)
  have hot : 2 ≤ H j := (le_max_left _ _).trans heat
  have u1 : 1 ≤ u := by linarith only [hot,rise]
  have up : 0<u := zero_lt_one.trans_le u1
  have spare : 8/u ≤ κ := (div_le_iff₀ up).mpr (by
    have far := (le_max_right _ _).trans (heat.trans rise)
    nlinarith only [(div_le_iff₀ kp).mp far])
  have grain : Beaming.grain (R.alloy.B.a.clock.J (j+1)) ≤ 1 := by
    unfold Beaming.grain
    apply (div_le_one (by positivity)).mpr
    have nonneg : (0:ℝ) ≤ R.alloy.B.a.clock.J (j+1) := by positivity
    linarith
  have stage : B (j+1) ≤ u :=
    (min_le_right _ _).trans ((Real.rpow_le_rpow_of_exponent_le u1 grain).trans_eq (Real.rpow_one u))
  obtain ⟨low,high⟩ := (R.makes.wilson.represents N per j jN).band
  change H j / 2 ≤ y at low
  change y ≤ 2*H j at high
  have yp : 0<y := by linarith only [low,hot]
  have yp' := Real.sqrt_pos.mpr yp
  have angular : u⁻¹ ≤ 3*regulatorRun R.family N per j := by
    change u⁻¹ ≤ 3*(Real.sqrt y)⁻¹
    rw [←one_div,←div_eq_mul_inv,div_le_div_iff₀ up yp',one_mul]
    nlinarith only [high,rise,u1,Real.sq_sqrt yp.le,sq_nonneg (u-1),sq_nonneg (Real.sqrt y-1)]
  have desc : -(order:ℝ) ≤ -((q:ℝ)+2) := by exact_mod_cast (show -((order:ℤ)) ≤ -((q:ℤ)+2) by omega)
  calc
    _ ≤ 8*u*(u^(-((q:ℝ)+2))) := mul_le_mul (mul_le_mul_of_nonneg_left stage (by norm_num))
      (Real.rpow_le_rpow_of_exponent_le u1 desc) (Real.rpow_nonneg up.le _) (by positivity)
    _ = (8/u)*(u⁻¹)^q := by
      rw [Real.rpow_neg up.le,Real.rpow_add up,Real.rpow_natCast,Real.rpow_two,inv_pow]
      field_simp
    _ ≤ _ := mul_le_mul spare (pow_le_pow_left₀ (inv_nonneg.mpr up.le) angular _) (pow_nonneg (inv_nonneg.mpr up.le) _) kp.le

end YM.Integration.WilsonReceivedCloseCalibratedBudget
