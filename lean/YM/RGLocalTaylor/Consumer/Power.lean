import YM.RGLocalTaylor.Mayer.Calendar

/-! # Recover actual g-power after the local costs in the E6 norm.

Use literal margin `7/16` per Taylor power in β⁻¹ units. No loss
scaling with computation order hidden in the conversion; can pay any
extra FIXED powers already suffered in re-expression by setting the
internal order. No convention change to a continuum/PT scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Mayer
open Pressure RG Wilson Lattice
open scoped Topology BigOperators Classical
variable {G : Gauge} {x b u : ℝ} {L:Side} {n d : ℕ}

lemma pay_extra (he : 1 ≤ x) (hb : 0<b) (hu : b ≤ 2*x) (hd : 8*d ≤ 7*n) :
    ((x^height)^n)⁻¹ ≤ Real.sqrt 2^d*(Real.sqrt b)⁻¹^d := by
  let y:= Real.sqrt x; have hY:0<x:=zero_lt_one.trans_le he
  have hy:0<y:=Real.sqrt_pos.mpr hY
  have hR: ((x^height)^n)⁻¹ ≤ (x^(-(1/2):ℝ))^d:= by
    rw [← Real.rpow_mul_natCast hY.le,← Real.rpow_neg hY.le,← Real.rpow_mul_natCast hY.le]
    apply Real.rpow_le_rpow_of_exponent_le he; unfold height; have hh : 8*(d:ℝ) ≤ 7*(n:ℝ):= by exact_mod_cast hd
    linarith
  apply hR.trans; rw [Real.rpow_neg hY.le, ← Real.sqrt_eq_rpow, ← mul_pow]; apply pow_le_pow_left₀ (inv_nonneg.mpr hy.le)
  rw [←div_eq_mul_inv,le_div_iff₀ (Real.sqrt_pos.mpr hb), mul_comm,←div_eq_mul_inv,div_le_iff₀ hy,←Real.sqrt_mul zero_le_two]; exact Real.sqrt_le_sqrt hu

lemma advance (he : 1<x)(hb : x/2≤b)(hp : d≤n):
    (Real.sqrt b)⁻¹^n ≤ Real.sqrt 2^(n-d)*(Real.sqrt b)⁻¹^d := by
  set y:= (Real.sqrt b)⁻¹
  have hu : 0<b:= by linarith
  have hr : 0 < Real.sqrt 2:=by positivity
  have hz : y ≤ Real.sqrt 2:= by unfold y; rw [inv_le_comm₀ (Real.sqrt_pos.mpr hu) hr, ← Real.sqrt_inv]; apply Real.sqrt_le_sqrt; linarith only [hb,he]
  nth_rw 1 [← Nat.sub_add_cancel hp]; rw [pow_add]
  have hh:0≤y:=by unfold y; positivity
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hh hz _) (pow_nonneg hh _)
end YM.RGLocalTaylor.Mayer
