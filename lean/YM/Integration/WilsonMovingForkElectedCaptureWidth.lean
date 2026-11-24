import YM.Integration.WilsonAddressedPublicFirstRoseCaptureWidth

/-! Capture a polynomially displaced exterior with its original group and
physical block. The fixed support constant is selected before the cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingForkElectedCaptureWidth
open Filter Lattice RG Wilson PhysicalNext.Repeat.Legato
variable {G : Gauge} (R : Run G)
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a

theorem variableWidth (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {j c d e : ℕ} {r M : ℝ} (rp : 0 < r) (mp : 0 < M) (before : c ≤ j)
    (captured : a (c+1) < M*r) (extent : 3*M ≤ (H j)^e) (scale : r ≤ (H j)^d*a j) :
    a c/a j ≤ (H j)^(d+e+1) := by
  have hp : 0 ≤ H j := zero_le_one.trans (R.family.path.levels.fits.delayed j).le
  have step : a c = ((R.family.S.block c).val:ℝ)*a (c+1) := by
    rw [R.family.S.a_step,mul_div_cancel₀ _ (by exact_mod_cast (R.family.S.block c).property.ne')]
  have paid : ((R.family.S.block c).val:ℝ)*M ≤ (H j)^(e+1) := by
    calc
      _ ≤ (3*H j)*M := mul_le_mul_of_nonneg_right
        (WilsonAddressedPublicFirstRoseCaptureWidth.block R simple slow before) mp.le
      _ = (3*M)*(H j) := by ring
      _ ≤ _ := by rw [pow_succ]; exact mul_le_mul_of_nonneg_right extent hp
  rw [div_le_iff₀ (R.family.S.a_pos j),step]
  calc
    _ ≤ ((R.family.S.block c).val:ℝ)*(M*r) :=
      mul_le_mul_of_nonneg_left captured.le (Nat.cast_nonneg _)
    _ ≤ (H j)^(e+1)*r := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right paid rp.le
    _ ≤ (H j)^(e+1)*((H j)^d*a j) := mul_le_mul_of_nonneg_left scale (pow_nonneg hp _)
    _ = (H j)^(d+e+1)*a j := by simp only [pow_add,pow_one];ring

theorem original (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {j c d B : ℕ} {r L T : ℝ} (rp : 0 < r) (lp : 0 ≤ L) (tp : 0 ≤ T)
    (before : c ≤ j) (captured : a (c+1) < (16*(1+L*T))*r)
    (fixed : 48*(1+L) ≤ H j) (pace : T ≤ (H j)^(2*B)) (scale : r ≤ (H j)^d*a j) :
    a c/a j ≤ (H j)^(d+2*B+2) := by
  have one : 1 ≤ (H j)^(2*B) := one_le_pow₀ (R.family.path.levels.fits.delayed j).le
  have area : 1+L*T ≤ (1+L)*(H j)^(2*B) := by
    calc
      _ ≤ (H j)^(2*B) + L*(H j)^(2*B) := add_le_add one (mul_le_mul_of_nonneg_left pace lp)
      _ = _ := by ring
  have extent : 3*(16*(1+L*T)) ≤ (H j)^(2*B+1) := by
    calc
      _ ≤ (48*(1+L))*(H j)^(2*B) := by linarith
      _ ≤ (H j)*(H j)^(2*B) := mul_le_mul_of_nonneg_right fixed (by positivity)
      _ = _ := by rw [pow_succ,mul_comm]
  have paid := variableWidth R simple slow rp (show 0 < 16*(1+L*T) by positivity)
    before captured extent scale
  simpa only [Nat.add_assoc] using paid

end YM.Integration.WilsonMovingForkElectedCaptureWidth
