import YM.Integration.WilsonInvariantActionPromotedQuota
import YM.Next.RANK.Insiders

/-! The original spatial capture charges the same promoted F/J deposits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionCaptureCharge
open Function Filter Finset Lattice Wilson RG Source Labels PhysMS RG17 FullVolume Spec
open Next.Rank PhysicalNext.Repeat.Legato Next.UVStress
open scoped BigOperators Classical
variable {G:Gauge}

theorem amount (C:Family G) (d k N per:ℕ) (x:C.label d):
    Spindle.paid C d k N per x=(C.S.a k^d)⁻¹*quota C d k N per x:=by
  have ap:=C.S.a_pos k
  unfold Spindle.paid Price.awake quota Frame.coeffSize
  simp only [Pi.smul_apply,norm_smul,norm_inv,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos ap,mul_sum]
  rfl

theorem admitted (C:Family G) {d k N per:ℕ} {M:ℝ} (x:C.label d)
    (paid:quota C d k N per x≤C.S.a k^d*M):
    Spindle.paid C d k N per x≤M:=by
  rw [amount]
  have ap:=pow_pos (C.S.a_pos k) d
  simpa only [←mul_assoc,inv_mul_cancel₀ ap.ne',one_mul] using
    mul_le_mul_of_nonneg_left paid (inv_pos.mpr ap).le

end YM.Integration.WilsonInvariantActionCaptureCharge
