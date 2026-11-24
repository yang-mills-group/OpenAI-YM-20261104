import YM.Integration.WilsonMatrixTicketLanesReportedWindow
import YM.Integration.WilsonCoherentInheritedSpool

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedAccuracy
open Function Filter Set Real RG Next.Rank OPE RG12 Extraction Spec Wilson
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G)

/-- The global original upper-coupling estimate costs one extra inverse half power
of the measured temperature, uniformly in the period and the future ultraviolet date. -/
theorem small (simple : G.Simple) (ε : ℝ) (pos : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,∀ N p,m ≤ N → regulatorRun R.family N p m ≤ ε := by
  let B := R.family.path.levels.clock.hatBeta
  have grows := Station.hat_rate R.family.path.levels simple
  have tends : Tendsto (fun m=> (Real.sqrt (B m/2))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp (grows.atTop_div_const zero_lt_two))
  filter_upwards [tends.eventually (gt_mem_nhds pos)] with m low N p future
  have bp : 0 < B m/2 := half_pos (zero_lt_one.trans (R.family.path.levels.fits.delayed m))
  have band : B m/2 ≤ R.family.path.β N p m := (R.makes.wilson.represents N p m future).band.1
  exact (inv_anti₀ (Real.sqrt_pos.mpr bp) (Real.sqrt_le_sqrt band)).trans low.le

/-- Exact cancellation between a thermal reserve and two authentic positive powers
of the running coupling. -/
theorem thermal (m N p : ℕ) (future : m ≤ N) :
    R.family.path.levels.clock.hatBeta m * regulatorRun R.family N p m^2 ≤ 2 := by
  let b := R.family.path.β N p m
  let g := regulatorRun R.family N p m
  have band : R.family.path.levels.clock.hatBeta m/2 ≤ b := (R.makes.wilson.represents N p m future).band.1
  have bp : 0 < b := Overlay.beta_positive R.makes.wilson future
  have exactHeat : b*g^2 = 1 := by
    change b * (Real.sqrt b)⁻¹^2 = 1
    rw [inv_pow,Real.sq_sqrt bp.le,mul_inv_cancel₀ bp.ne']
  change _ * g^2 ≤ 2
  calc
    _ ≤ (2*b)*g^2 := mul_le_mul_of_nonneg_right (by linarith only [band]) (sq_nonneg _)
    _ = _ := by rw [mul_assoc,exactHeat,mul_one]

/-- Paying all honest field costs, and the true logarithmic Taylor cost at the
previous block, by finitely many extra coefficients gives every prescribed
relative accuracy on every subsequent period and cutoff. -/
theorem coupon (simple : G.Simple) (q e : ℕ) (A ε : ℝ) (nonneg : 0 ≤ A) (pos : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,∀ b N p,b ≤ m → m ≤ N →
      A * R.family.path.levels.clock.hatBeta m^e *
        (regulatorRun R.family N p m^(q+2*(e+1)+1) *
          (2+Real.log (R.family.path.levels.clock.hatBeta b))) ≤
      ε * regulatorRun R.family N p m^q := by
  let C := 3*A*(2:ℝ)^(e+1)
  have cn : 0 ≤ C := by positivity
  have cp : 0 < C+1 := by positivity
  filter_upwards [small R simple (ε/(C+1)) (div_pos pos cp)] with m allowed b N p past future
  let B := R.family.path.levels.clock.hatBeta
  let g := regulatorRun R.family N p m
  have bp : 1 ≤ B m := (R.family.path.levels.fits.delayed m).le
  have gp : 0 ≤ g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have short : 2+Real.log (B b) ≤ 3*B m := by
    have mono : B b ≤ B m :=
      WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le past
    linarith only [Real.log_le_self (zero_lt_one.trans (R.family.path.levels.fits.delayed b)).le,mono,bp]
  have low : C*g ≤ ε := (mul_le_mul_of_nonneg_right (by linarith : C≤C+1) gp).trans
    (by simpa only [mul_comm (C+1) g] using (le_div_iff₀ cp).mp (allowed N p future))
  have bound : (B m*g^2)^(e+1) ≤ (2:ℝ)^(e+1) :=
    pow_le_pow_left₀ (mul_nonneg (zero_le_one.trans bp) (sq_nonneg _)) (thermal R m N p future) _
  change A*B m^e*(g^(q+2*(e+1)+1)*(2+Real.log (B b))) ≤ ε*g^q
  calc
    _ ≤ A*B m^e*(g^(q+2*(e+1)+1)*(3*B m)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left short (pow_nonneg gp _))
        (mul_nonneg nonneg (pow_nonneg (zero_le_one.trans bp) _))
    _ = (3*A*(B m*g^2)^(e+1)*g)*g^q := by
      simp only [pow_add,pow_mul,mul_pow,pow_one]
      ring
    _ ≤ (C*g)*g^q := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left bound (mul_nonneg (by norm_num) nonneg)) gp) (pow_nonneg gp _)
    _ ≤ _ := mul_le_mul_of_nonneg_right low (pow_nonneg gp _)

end YM.Integration.WilsonMatrixTicketLanesReportedAccuracy
