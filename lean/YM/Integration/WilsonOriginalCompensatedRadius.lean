import YM.Integration.WilsonMovingMentorPageRefund
import YM.QuadraticLocal.Pique

/-! The two consecutive physical Page credits set one contracting marker radius
before the upper cutoff, volume, paid row, or test. Its inverse on each fixed
number of occupied marks consumes an arbitrarily small temperature exponent. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalCompensatedRadius
open Filter RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato QuadraticLocal
open scoped Topology

variable {G:Gauge} (R:Run G)
local notation "cap" => WilsonMovingMentorPageRefund.cap R
local notation "β̂" => R.alloy.B.a.clock.hatBeta

def scale (i:ℕ) : ℝ := (cap (i+1))^6 * cap i

theorem page (i:ℕ) : 1 ≤ cap i := by
  exact Real.one_le_rpow (R.alloy.B.a.fits.delayed (i+1)).le
    (by unfold Beaming.grain; positivity)

theorem floor (i:ℕ) : 1 ≤ scale R i := by
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (page R _) ) (page R _)

theorem hard {i:ℕ} {Ω:ℝ} (low:0 ≤ Ω) (registered:Ω ≤ cap (i+1)) :
    Ω^6 ≤ scale R i := by
  exact (pow_le_pow_left₀ low registered 6).trans
    (le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans (page R _)) _) (page R _))

/-- The actual rebated printed wallet can afford the next registered Page.
Both expenses and the row mass may be instantiated after the cutoff. -/
theorem salary {i:ℕ} {Ω z f c Ω':ℝ} (first:0<Ω) (next:0<Ω')
    (rebate:z ≤ cap (i+1)) (zpos:0≤z) (output:f ≤ Ω) (small:c ≤ Ω⁻¹) (pos:0≤c)
    (second:Ω' ≤ cap i) :
    (scale R i)⁻¹*(z*(f*c)) ≤ Ω'⁻¹ := by
  have fc:f*c ≤ 1 := (mul_le_mul_of_nonneg_right output pos).trans
    ((mul_le_mul_of_nonneg_left small first.le).trans_eq (mul_inv_cancel₀ first.ne'))
  have zc:z*(f*c) ≤ cap (i+1) := (mul_le_of_le_one_right zpos fc).trans rebate
  have M:=page R (i+1)
  have pm:cap (i+1) ≤ (cap (i+1))^6 := by
    simpa only [pow_one] using pow_le_pow_right₀ M (by decide : 1≤6)
  have total:cap (i+1)*Ω' ≤ scale R i :=
    mul_le_mul pm second next.le (pow_nonneg (zero_le_one.trans M) _)
  have hs:0<scale R i := zero_lt_one.trans_le (floor R i)
  have convert : (scale R i)⁻¹*cap (i+1) ≤ Ω'⁻¹ := by
    rw [inv_mul_eq_div,←one_div]
    exact (div_le_div_iff₀ hs next).mpr (by simpa using total)
  exact (mul_le_mul_of_nonneg_left zc (inv_nonneg.mpr hs.le)).trans convert

theorem powers (simple:G.Simple) (h:ℕ) {δ:ℝ} (positive:0<δ) :
    ∀ᶠ i:ℕ in atTop, (scale R i)^h ≤ (β̂ (i+2))^δ := by
  have shift: Tendsto (fun i:ℕ=>i+1) atTop atTop := tendsto_add_atTop_nat 1
  have half:0<δ/2 := half_pos positive
  filter_upwards [WilsonMovingMentorPageReserve.powers R simple h half,
    shift.eventually (WilsonMovingMentorPageReserve.powers R simple (6*h) half)] with i lower upper
  have start: 0< β̂ (i+2) := zero_lt_one.trans (R.alloy.B.a.fits.delayed _)
  have raises:β̂ (i+1) ≤ β̂ (i+2) := by
    rw [Push.PriceCompiler.beta_eq R.alloy.B.valid (i+1)]
    exact le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
  have first := upper (cap (i+1)) (zero_le_one.trans (page R _)) le_rfl
  have second := (lower (cap i) (zero_le_one.trans (page R _)) le_rfl).trans
    (Real.rpow_le_rpow (zero_le_one.trans (R.alloy.B.a.fits.delayed _).le) raises half.le)
  rw [scale,mul_pow,←pow_mul]
  calc
    _ ≤ (β̂ (i+2))^(δ/2) * (β̂ (i+2))^(δ/2) :=
      mul_le_mul first second (pow_nonneg (zero_le_one.trans (page R _)) _) (Real.rpow_nonneg start.le _)
    _ = _ := by rw [←Real.rpow_add start,add_halves]

end YM.Integration.WilsonOriginalCompensatedRadius
