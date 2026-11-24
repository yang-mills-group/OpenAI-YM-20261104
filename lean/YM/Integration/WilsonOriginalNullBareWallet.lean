import YM.Integration.WilsonOriginalNullBareFunding

/-! Restore the actual single marked socket and its actual profile only once at birth. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareWallet

theorem restored {β H w A B D C s a b:ℝ} {n:ℕ}
    (warm:1 ≤ β) (fit:β ≤ H) (wp:0<w) (profile:0 ≤ s)
    (step:a ≤ 1) (wage:b ≤ 1)
    (pay:A ≤ β^b*(1+s)) (radius:w⁻¹ ≤ β^a*(1+A))
    (earned:w*(B+D) ≤ C*(1+H)^n):
    B+D ≤ 2*|C| *(1+H)^(n+2)*(1+s) :=by
  let h:=1+H
  have hp:0 ≤ h:=by dsimp [h];linarith only [warm,fit]
  have h1:1 ≤ h:=by dsimp [h];linarith only [warm,fit]
  have βh:β ≤ h:=by dsimp [h];linarith only [fit]
  have sa:β^a ≤ h:=((Real.rpow_le_rpow_of_exponent_le warm step).trans_eq (Real.rpow_one _)).trans βh
  have sb:β^b ≤ h:=((Real.rpow_le_rpow_of_exponent_le warm wage).trans_eq (Real.rpow_one _)).trans βh
  have aa:1+A ≤ 2*h*(1+s):=by
    have p:=pay.trans (mul_le_mul_of_nonneg_right sb (by positivity))
    have q:1 ≤ h*(1+s):=one_le_mul_of_one_le_of_one_le h1 (by linarith)
    nlinarith only [p,q]
  have rr:w⁻¹ ≤ 2*h^2*(1+s):=calc
    w⁻¹ ≤ β^a*(1+A):=radius
    _ ≤ β^a*(2*h*(1+s)):=mul_le_mul_of_nonneg_left aa (Real.rpow_nonneg (zero_le_one.trans warm) _)
    _ ≤ h*(2*h*(1+s)):=mul_le_mul_of_nonneg_right sa (by positivity)
    _ = _:=by ring
  have upper:w*(B+D) ≤ |C| *h^n:=earned.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  calc
    _ = w⁻¹*(w*(B+D)):=by rw [←mul_assoc,inv_mul_cancel₀ wp.ne',one_mul]
    _ ≤ w⁻¹*(|C| *h^n):=mul_le_mul_of_nonneg_left upper (inv_nonneg.mpr wp.le)
    _ ≤ (2*h^2*(1+s))*(|C| *h^n):=mul_le_mul_of_nonneg_right rr (by positivity)
    _ = _:=by dsimp [h];rw [pow_add];ring
end YM.Integration.WilsonOriginalNullBareWallet
