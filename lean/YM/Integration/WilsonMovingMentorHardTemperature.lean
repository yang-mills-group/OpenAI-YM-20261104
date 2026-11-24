import YM.Integration.WilsonMovingMentorPageReserve

/-! Conversion of a hard Wilson salary at its represented physical temperature. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingMentorHardTemperature
open RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ConnectedActivityE6

theorem measured {G : Gauge} (R : Run G) {m N : ℕ} (live : m≤N) (per slots q : ℕ) :
    let x := R.alloy.B.a.clock.hatBeta m
    let g := Coat.gStep (R.family.path.rep N per m).beta
    g^(q+2*slots)*x^slots ≤ g^q*(2:ℝ)^slots := by
  let x := R.alloy.B.a.clock.hatBeta m
  let β := (R.family.path.rep N per m).beta
  let g := Coat.gStep β
  change g^(q+2*slots)*x^slots ≤ g^q*2^slots
  obtain ⟨lo,hi⟩ := (R.makes.wilson.represents N per m live).band
  change x/2 ≤ β at lo
  change β ≤ 2*x at hi
  have xp : 0 ≤ x := by linarith
  have gp : 0 ≤ g := inv_nonneg.mpr (Real.sqrt_nonneg β)
  have unit : g^2*β ≤ 1 := by
    by_cases warm : 0<β
    · simp [g,Coat.gStep,inv_pow,Real.sq_sqrt warm.le,warm.ne']
    · simp [g,Coat.gStep,Real.sqrt_eq_zero_of_nonpos (le_of_not_gt warm)]
  have coarse : g^2*x ≤ 2 := calc
    g^2*x ≤ g^2*(2*β) := mul_le_mul_of_nonneg_left (by linarith only [lo]) (sq_nonneg g)
    _ ≤ 2 := by linarith [unit]
  calc
    g^(q+2*slots)*x^slots = g^q*(g^2*x)^slots := by rw [pow_add,pow_mul,mul_pow]; ring
    _ ≤ g^q*2^slots := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (sq_nonneg g) xp) coarse slots) (pow_nonneg gp q)

end YM.Integration.WilsonMovingMentorHardTemperature
end
