import YM.Integration.WilsonOriginalAlternativeTrialCollateral

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialSpan
open WilsonOriginalAlternativeTrialCollateral

theorem original {H C:ℝ}{u f K a:ℕ}(h:1≤H)
    (outer:((f-u:ℕ):ℝ)≤C*(1+Real.log H))
    (inner:((K-f:ℕ):ℝ)*Real.log 2≤(a:ℝ)*Real.log H):
    ((f-u+reserve K f:ℕ):ℝ)≤(C+72*((a:ℝ)/Real.log 2)+48)*(1+Real.log H):=by
  have lp:0<Real.log 2:=Real.log_pos (by norm_num)
  have l0:0≤Real.log H:=Real.log_nonneg h
  have ratio:((K-f:ℕ):ℝ)≤((a:ℝ)/Real.log 2)*Real.log H:=by
    calc ((K-f:ℕ):ℝ)≤(a:ℝ)*Real.log H/Real.log 2:=(le_div_iff₀ lp).2 inner
         _=((a:ℝ)/Real.log 2)*Real.log H:=by ring
  have a0:0≤(a:ℝ)/Real.log 2:=div_nonneg (Nat.cast_nonneg _) lp.le
  simp only [reserve,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  linarith only [outer,ratio,a0,l0,mul_nonneg (show (0:ℝ)≤48 by norm_num) l0]

end YM.Integration.WilsonOriginalAlternativeTrialSpan
end
