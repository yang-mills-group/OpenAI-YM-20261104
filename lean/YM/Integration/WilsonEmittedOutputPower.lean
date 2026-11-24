import YM.Integration.WilsonEmittedRootedFinance
/-! The degrees needed for the signed protected group-field replacement, with the cash and pole of the actual source explicit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedOutputPower
open Real RG Wilson
def constant (T:ℕ):ℝ := (2*T:ℕ)*(1+(2:ℝ)^T)+4^T

theorem tail {H β:ℝ} (hp:0<H) (bb:0<β) (upper:β≤2*H)
    (g:ℝ) (showed:g=(Real.sqrt β)⁻¹) (g1:g≤1) (T:ℕ) :
    (H^T)⁻¹ ≤ (2:ℝ)^T*g^T := by
  have g0:0<g:=showed.symm ▸ inv_pos.mpr (Real.sqrt_pos.mpr bb)
  have v:g^2=β⁻¹:=by rw [showed,inv_pow,Real.sq_sqrt bb.le]
  have base:H⁻¹ ≤ 2*g^2:=by
    rw [v,←div_eq_mul_inv,←one_div]
    apply (div_le_div_iff₀ hp bb).mpr
    linarith
  have line:H⁻¹≤2*g:=base.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr g1) g0.le])
  rw [←inv_pow,←mul_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr hp.le) line T

theorem width {g W:ℝ} (hg:0<g) (hp:0≤W) (held:W≤2*g^(1/2:ℝ)) (T:ℕ) :
    W^(2*T)≤4^T*g^T := by
  have v:(g^(1/2:ℝ))^2=g:=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hg.le];norm_num
  have s:=pow_le_pow_left₀ hp held 2
  rw [mul_pow,v] at s
  rw [pow_mul,←mul_pow]
  exact pow_le_pow_left₀ (sq_nonneg _) (by simpa only [show (2:ℝ)^2=4 by norm_num] using s) _

/-- The angular cancellation at degree 3T, tested through degree 2T, after the two real rooted fare payments. -/
theorem retained {g W h gp a b A τ:ℝ} (T:ℕ) (hg:0<g) (hW:0≤W) (gp0:0≤gp) (A0:0≤A)
    (zero:h*|gp| *a≤A) (far:h*|gp| *b≤A*τ)
    (held:W≤2*g^(1/2:ℝ)) (short:τ≤(2:ℝ)^T*g^T) :
    h*(gp*((2*T:ℕ)*(a*g^(3*T-2*T)+b)+a*W^(2*T)))≤constant T*A*g^T := by
  rw [show 3*T-2*T=T by omega]
  have h₀:=mul_le_mul_of_nonneg_right zero (pow_nonneg hg.le T)
  have h₁:=far.trans (mul_le_mul_of_nonneg_left short A0)
  have h₂:=mul_le_mul zero (width hg hW held T) (pow_nonneg hW _) A0
  calc
    h*(gp*(((2*T:ℕ):ℝ)*(a*g^T+b)+a*W^(2*T))) =
      (2*T:ℕ)*((h*|gp| *a)*g^T+(h*|gp| *b))+(h*|gp| *a)*W^(2*T):=by rw [abs_of_nonneg gp0];ring
    _ ≤ (2*T:ℕ)*(A*g^T+A*((2:ℝ)^T*g^T))+A*(4^T*g^T):=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add h₀ h₁) (by positivity)) h₂
    _ = constant T*A*g^T:=by unfold constant;ring

theorem paid {H β g:ℝ} (bb:0<β) (lower:H/2≤β) (H0:0<H) (heard:g=(Real.sqrt β)⁻¹)
    {D pole q:ℕ} {wallet C M:ℝ} (cp:0≤C) (mp:0≤M) (cash:wallet≤C*H^D*M)
    (T:ℕ) (chosen:T=2*D+pole+1+(q+3)) :
    (g^pole)⁻¹ * (constant T*(wallet*g⁻¹)*g^T) ≤ (constant T*C*2^D)*M*g^(q+3) := by
  have g0:0<g:=heard.symm ▸ inv_pos.mpr (Real.sqrt_pos.mpr bb)
  have g2:g^2=β⁻¹:=by rw [heard,inv_pow,Real.sq_sqrt bb.le]
  have delta: H*g^2≤2:=by rw [g2,←div_eq_mul_inv,div_le_iff₀ bb];linarith
  have plan:H^D*g^(2*D)≤(2:ℝ)^D:=by
    rw [pow_mul,←mul_pow];exact pow_le_pow_left₀ (mul_nonneg H0.le (sq_nonneg _)) delta D
  have hold:wallet*g^(2*D)≤C*2^D*M:=by
    calc
      _ ≤ C*H^D*M*g^(2*D):=mul_le_mul_of_nonneg_right cash (pow_nonneg g0.le _)
      _ = C*(H^D*g^(2*D))*M:=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left plan cp) mp
  have C0:0≤constant T:=by unfold constant;positivity
  have expand:g^T=g^(2*D)*g^pole*g*g^(q+3):=by rw [chosen,pow_add,pow_add,pow_add,pow_one]
  calc
    _ = constant T*(wallet*g^(2*D))*g^(q+3):=by rw [expand];field_simp
    _ ≤ constant T*(C*2^D*M)*g^(q+3):=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hold C0) (pow_nonneg g0.le _)
    _ = _:=by ring

end YM.Integration.WilsonEmittedOutputPower
end
