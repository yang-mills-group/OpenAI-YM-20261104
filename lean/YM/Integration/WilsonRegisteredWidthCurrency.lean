import YM.Integration.WilsonRegisteredCenteredReading
import YM.Integration.WilsonAdmissionScale
import YM.RG12.Common.Short

/-! Uniform numerical size of the genuine earlier normalized angular
reach and its two original grade-four material costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredWidthCurrency
open Filter Lattice RG Wilson Precision PertExtension PhysicalNext.Repeat.Legato Pert.Asymptotics RG16
open WilsonRegisteredAffineSource WilsonRegisteredCenteredReading WilsonInheritedRegisteredField
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels

theorem band (N per k:ℕ) (live:k ≤ N) :
    let s:=Real.log ((A).clock.hatBeta k)
    let Z:=(A).clock.monitor k
    0 ≤ width R N per k ∧ s^2/64 ≤ width R N per k*Z ∧ width R N per k*Z ≤ s^2/16 := by
  intro s Z
  let g:=regulatorRun R.family N per k
  let gh:=(A).clock.hatCoupling k
  have same:(R.family.path.rep N per k).p=(A).budget k:=(R.makes.wilson.represents N per k live).vac
  have gp:0<gh:=inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans ((A).fits.delayed k)))
  have zp:0<Z:=Real.exp_pos _
  have actual:gh ≤ 2*g ∧ g ≤ 2*gh:=IterationFour.Currency.hat_g R.makes N per k live
  have g0:0 ≤ g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have eq:width R N per k=(g*(s^2/32))/(gh*Z):=by unfold width;rw [same];rfl
  have whole:width R N per k*Z=(g/gh)*(s^2/32):=by rw [eq];field_simp [gp.ne',zp.ne']
  have lo:(1:ℝ)/2 ≤ g/gh:=(le_div_iff₀ gp).2 (by linarith only [actual.1])
  have hi:g/gh ≤ 2:=(div_le_iff₀ gp).2 actual.2
  constructor
  · rw [eq];positivity
  rw [whole]
  constructor
  · exact (show s^2/64=(1/2)*(s^2/32) by ring).le.trans (mul_le_mul_of_nonneg_right lo (by positivity))
  · exact (mul_le_mul_of_nonneg_right hi (show 0 ≤ s^2/32 by positivity)).trans_eq (by ring)

theorem logarithmic (simple:G.Simple) (d:ℕ) {ε:ℝ} (he:0<ε) :
    ∀ᶠ k:ℕ in atTop,∀N per (_live:k ≤ N),
    let s:=Real.log ((A).clock.hatBeta k)
    s^d*width R N per k ≤ ε := by
  have logs:=Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate (A) simple)
  filter_upwards [logs.eventually_ge_atTop ε⁻¹, (Real.tendsto_log_atTop.comp logs).eventually_ge_atTop ((d:ℝ)+3)]
    with k large high N per live s
  let Z:=(A).clock.monitor k
  let y:=Real.log s
  have sp:0<s:=Real.log_pos ((A).fits.delayed k)
  have zp:0<Z:=Real.exp_pos _
  have high':(d:ℝ)+3 ≤ y:=high
  have y0:0 ≤ y:=by linarith only [high',Nat.cast_nonneg (α:=ℝ) d]
  have expBound:s^(d+3) ≤ Z:=by
    change s^(d+3) ≤ Real.exp (y^2)
    rw [←Real.exp_log sp,←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    change ((d+3:ℕ):ℝ)*y ≤ y^2
    push_cast
    nlinarith only [mul_nonneg y0 (sub_nonneg.mpr high')]
  have first:=band R N per k live
  have budget:width R N per k*Z ≤ s^2:=first.2.2.trans (by nlinarith only [sq_nonneg s])
  have one:width R N per k*s^(d+3) ≤ s^2:=(mul_le_mul_of_nonneg_left expBound first.1).trans budget
  have spent:(s^d*width R N per k)*s ≤ 1:=by
    apply (le_of_mul_le_mul_right _ (sq_pos_of_pos sp))
    calc _ = width R N per k*s^(d+3) :=by rw [pow_add];ring
         _  ≤  s^2:=one
         _ = _:=by ring
  have cash:1 ≤ ε*s:=by
    calc 1=ε*ε⁻¹:=(mul_inv_cancel₀ he.ne').symm
         _ ≤ ε*s:=mul_le_mul_of_nonneg_left large he.le
  exact le_of_mul_le_mul_right (spent.trans cash) sp

end YM.Integration.WilsonRegisteredWidthCurrency
end
