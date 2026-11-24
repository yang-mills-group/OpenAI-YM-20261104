import YM.Integration.WilsonIndependentRawWordOrbit

/-! At the terminal page the true side bound turns each infrared
remainder into an inverse power of the original top side. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentRawPeriodPower
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Taping Lattice
variable {W:Type}{M:W→ℕ}{n:Page M→Side}{G:Gauge}{S:Heir n G}

def terminal (M:W→ℕ):Choice M:=⟨M,le_rfl⟩

theorem cost (V:Reel S)(γ:ℝ)(lo:0<γ)(hi:γ<1)(b K:ℕ)(hb:0<b)
    (start:∀ w,S.l (Page.opening M w)=1)
    (side:∀ w,(n (Page.finallyW M w)).val≤K)(w:W) :
    S.modifyErr 0 b γ (terminal M) w ≤ (2+(K:ℝ)^γ)*(S.P w) ^ (-(γ/2)) := by
  let P:=S.P w
  let l:=S.l (Page.finallyW M w)
  have hp:0<P:=S.hp w
  have up:1≤P := by
    have H:=V.phase (Page.opening M w)
    change S.l (Page.opening M w)*(n (Page.opening M w)).val=P at H
    rw [start w,one_mul] at H
    rw [←H]
    exact_mod_cast (n (Page.opening M w)).property
  have hl:0<l:=S.hl _
  have npos:0≤(K:ℝ):=Nat.cast_nonneg _
  have geom:P≤(K:ℝ)*l := by
    have H:=V.phase (Page.finallyW M w)
    change l*(n (Page.finallyW M w)).val=P at H
    rw [←H,mul_comm]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast side w) hl.le
  have hb':(1:ℝ)≤b:=by exact_mod_cast hb
  have gB : (P^b)⁻¹ ≤ (P^(γ/2))⁻¹ := by
    apply inv_anti₀ (Real.rpow_pos_of_pos hp _)
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le up (by linarith)
  have gL : (l^γ)⁻¹ ≤ (K:ℝ)^γ * (P^(γ/2))⁻¹ := by
    have priced : P^(γ/2) ≤ (K:ℝ)^γ*l^γ := by
      rw [←Real.mul_rpow npos hl.le]
      exact (Real.rpow_le_rpow_of_exponent_le up (by linarith : γ/2≤γ)).trans
        (Real.rpow_le_rpow hp.le geom lo.le)
    rw [←div_eq_mul_inv,le_div_iff₀ (Real.rpow_pos_of_pos hp _),inv_mul_eq_div]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hl _)).mpr priced
  change (S.ε w^0)⁻¹*(P^b)⁻¹+(P^(γ/2))⁻¹+(l^γ)⁻¹ ≤ _
  rw [pow_zero,inv_one,one_mul,Real.rpow_neg hp.le]
  linarith

end YM.Integration.WilsonIndependentRawPeriodPower
