import YM.Integration.WilsonPhysicalThermalWickGain

/-! The loss depends on the degree of the two submitted labels. The reserve
may be chosen at a higher degree before the infrared and ultraviolet limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickFineGain
open WilsonPhysicalThermalWickGain
open Filter Next.Rank Next.Rank.Perch Next.Rank.Glimmer Next.Rank.Common
open scoped Topology

theorem original (d k:ℕ)(shelf:100*(d+1)≤k)(C:ℝ)(cn:0≤C):
    ∀ᶠ s:ℝ in atTop,
      C*(error k s*priced (bill (fuel k 2) s+error k s) (2*d))+bill (-3/2) s≤bill (-127/128) s:=by
  let F:=fuel k 2
  let D:=2*d
  let e:ℝ:=-1+F/2
  let H:ℝ:=(4*((D:ℝ)+1))^D
  have fp:0<F:=fuel_real .. 
  have close:e+F*D< -127/128:=by
    have hk:100*((d:ℝ)+1)≤k:=by exact_mod_cast shelf
    dsimp [e,F,D,fuel]
    push_cast
    field_simp
    nlinarith
  have up:-3/2≤e+F*D:=by dsimp only [e];have pos:=mul_nonneg fp.le (Nat.cast_nonneg D);linarith
  have small:e≤0:=by have:=mul_nonneg fp.le (Nat.cast_nonneg D);linarith
  filter_upwards [transports close (C*H+1)] with s fee
  have B1:1≤bill F s:=costed F s fp.le
  have tiny:error k s≤1:=(power k s).le.trans ((billed s small).trans (bill_zero s).le)
  have E0:0≤error k s:=by rw [power];exact (Real.exp_pos _).le
  have large:priced (bill F s+error k s) D≤H*bill (F*D) s:=by
    rw [←bills]
    change ((2*(bill F s+error k s))*(D+1:ℝ))^D≤(4*(D+1:ℝ))^D*(bill F s)^D
    rw [←mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith only [mul_nonneg (sub_nonneg.mpr (tiny.trans B1)) (show 0≤(D:ℝ)+1 by positivity)]
  calc
    _≤C*(error k s*(H*bill (F*D) s))+bill (e+F*D) s:=
      add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left large E0) cn) (billed s up)
    _=(C*H+1)*bill (e+F*D) s:=by rw [show error k s=bill e s from power ..,←overlap e (F*D) s];ring
    _≤_:=fee

end YM.Integration.WilsonPhysicalThermalWickFineGain
end
