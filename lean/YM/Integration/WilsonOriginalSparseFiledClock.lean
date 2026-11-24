import YM.Integration.WilsonEmittedLengthWindow

/-! Spatial exponential for the two original compact pupils at their own rooted
radii.  The lower bound for the reporting clock does not use the physical side. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSparseFiledClock
open scoped BigOperators

theorem tail {H σ:ℝ} (pos:0 < σ) (reserve:Real.exp ((σ⁻¹)^2) ≤ H)
    (k:ℕ) (late:(512*((k:ℝ)+1))^2 ≤ Real.log H):
    Real.exp (-((σ/8)*(↑(Nat.ceil ((Real.log H)^2)/32:ℕ):ℝ))) ≤ (H^k)⁻¹:=by
  let s:=Real.sqrt (Real.log H)
  let B:=Nat.ceil ((Real.log H)^2)
  have lx:0 ≤ Real.log H:=(sq_nonneg _).trans late
  have ss:s^2=Real.log H:=Real.sq_sqrt lx
  have size:512*((k:ℝ)+1) ≤ s:=(Real.le_sqrt (by positivity) lx).mpr late
  have ls:512 ≤ s:=by linarith [show (0:ℝ) ≤ k by positivity]
  have sp:0 < s:=by linarith
  have Hpos:0 < H:=(Real.exp_pos _).trans_le reserve
  have hs:(σ⁻¹)^2 ≤ Real.log H:=by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) reserve
  have invs:σ⁻¹ ≤ s:=(Real.le_sqrt (inv_nonneg.mpr pos.le) lx).mpr hs
  have under:s⁻¹ ≤ σ:=by simpa only [inv_inv] using (inv_anti₀ (inv_pos.mpr pos) invs)
  have D:(Real.log H)^2 ≤ (B:ℝ):=Nat.le_ceil _
  have large:8 ≤ Real.log H:=by nlinarith [sq_nonneg (s-5)]
  have Bbig:64 ≤ B:=by exact_mod_cast (show (64:ℝ) ≤ B by nlinarith [sq_nonneg (Real.log H-8)])
  have Bm:B ≤ 64*(B/32):=by omega
  have volume:(Real.log H)^2 ≤ 64*(B/32:ℕ):=D.trans (by exact_mod_cast Bm)
  have rate:512*(k:ℝ)*s ≤ Real.log H:=by
    rw [←ss]; nlinarith [mul_nonneg (show 0 ≤ s-512*k by linarith) sp.le]
  have cash:(k:ℝ)*Real.log H ≤ (σ/8)*(B/32:ℕ):=by
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right under (by norm_num : (0:ℝ) ≤ 8)) (Nat.cast_nonneg _))
    have z:=mul_le_mul_of_nonneg_right rate lx
    field_simp [sp.ne']
    nlinarith
  calc
    _  ≤  Real.exp (-((k:ℝ)*Real.log H)) := Real.exp_le_exp.mpr (neg_le_neg cash)
    _ = (H^k)⁻¹ := by rw [Real.exp_neg,←Real.log_pow,Real.exp_log (pow_pos Hpos _)]

theorem funded {H σ C:ℝ} (pos:0 < σ) (reserve:Real.exp ((σ⁻¹)^2) ≤ H)
    (d p:ℕ) (nonnegative:0 ≤ C)(gross:C ≤ H^d)
    (late:(512*((d+p:ℕ)+1:ℝ))^2 ≤ Real.log H):
    Real.exp (-((σ/8)*(↑(Nat.ceil ((Real.log H)^2)/32:ℕ):ℝ)))*C ≤ (H^p)⁻¹:=by
  have Hpos:0 < H:=(Real.exp_pos _).trans_le reserve
  calc
    _  ≤  (H^(d+p))⁻¹*(H^d) := mul_le_mul (tail pos reserve (d+p) late) gross nonnegative (by positivity)
    _ = _ := by rw [pow_add];field_simp

end YM.Integration.WilsonOriginalSparseFiledClock
end
