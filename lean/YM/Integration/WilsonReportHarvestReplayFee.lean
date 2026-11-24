import YM.Integration.WilsonReportHarvestSourceReach

/-! The extra actual support depth pays each preceding temperature power
before the signed regular and forced entries are evaluated. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportHarvestReplayFee
open Real RG WilsonMeasuredAdmission WilsonReportHarvestSourceReach
variable {G:Gauge}
theorem purchased (A:Levels G)(j q D:ℕ){M δ:ℝ}(mp:0 ≤ M)
    (fee:M*Real.exp (-(D:ℝ)) ≤ δ):
    M*Real.exp (-((D+depth A (q:ℝ) 1 j:ℕ):ℝ)) ≤ δ/(A.clock.hatBeta j)^q:=by
  let T:=A.clock.hatBeta j
  let L:=depth A (q:ℝ) 1 j
  have tp:0<T:=zero_lt_one.trans (A.fits.delayed j)
  have scale:(q:ℝ)*Real.log T ≤ (L:ℝ):=calc
    _ ≤ (q:ℝ)*(mast A j):=by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
      change Real.log T ≤ 2+Real.log T;linarith
    _ ≤ (L:ℝ):=by change _≤(⌈(q:ℝ)*(mast A j)^1⌉₊:ℝ);rw [pow_one];exact Nat.le_ceil _
  have cash:T^q*Real.exp (-(L:ℝ)) ≤ 1:=by
    rw [←Real.exp_log (pow_pos tp q),Real.log_pow,←Real.exp_add,←Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith only [scale])
  apply (le_div_iff₀ (pow_pos tp q)).2
  have oldplus:0 ≤ M*Real.exp (-(D:ℝ)):=mul_nonneg mp (Real.exp_pos _).le
  calc (M*Real.exp (-((D+depth A (q:ℝ) 1 j:ℕ):ℝ)))*T^q
          = (M*Real.exp (-(D:ℝ)))*(T^q*Real.exp (-(L:ℝ))):=by
              change (M*Real.exp (-((D+L:ℕ):ℝ)))*T^q=_;rw [Nat.cast_add,neg_add,Real.exp_add];ring
       _ ≤ (M*Real.exp (-(D:ℝ)))*1:=mul_le_mul_of_nonneg_left cash oldplus
       _ ≤ δ:=by simpa only [mul_one] using fee

end YM.Integration.WilsonReportHarvestReplayFee
