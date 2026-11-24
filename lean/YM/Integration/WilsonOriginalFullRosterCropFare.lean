import YM.Integration.WilsonOriginalSeparatedFrontClusters

/-! Conversion of the original B/32 teacher purchase to a finite-roster crop. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFullRosterCropFare
open WilsonOriginalSeparatedFrontClusters

theorem blocks (B n:ℕ)(late:64*(n+1) ≤ B):B/32 ≤ crop B n*(4*(n+1)):=by
  let m:=crop B n
  let d:=64*(n+1)
  have dp:0<d:=by dsimp only [d]; positivity
  have start:1 ≤ m:=(Nat.le_div_iff_mul_le dp).2 (by simpa only [one_mul] using late)
  have division:B% d+d*m=B:=Nat.mod_add_div B d
  have left:B% d<d:=Nat.mod_lt B dp
  have top:B<d*(m+1):=by rw [Nat.mul_add,Nat.mul_one];omega
  have restore:d*(m+1) ≤ d*(2*m):=Nat.mul_le_mul_left d (by omega)
  have bank:d*(2*m)=32*(m*(4*(n+1))):=by dsimp only [d];ring
  have low:(B/32)*32 ≤ B:=Nat.div_mul_le_self B 32
  change B/32 ≤ m*(4*(n+1))
  omega

theorem original (B n P:ℕ){H σ:ℝ}(late:64*(n+1) ≤ B)(clock:0<H)(width:0<σ)
    (teacher:Real.exp (-(σ/4))^(B/32) ≤ (H^(P*(4*(n+1))))⁻¹):
    Real.exp (-(σ/4))^(crop B n) ≤ (H^P)⁻¹:=by
  let c:=Real.exp (-(σ/4))
  let D:=4*(n+1)
  have cold:c ≤ 1:=Real.exp_le_one_iff.mpr (by linarith)
  have price:(c^(crop B n))^D ≤ ((H^P)⁻¹)^D:=by
    rw [←pow_mul,inv_pow,←pow_mul]
    exact (pow_le_pow_of_le_one (Real.exp_pos _).le cold (blocks B n late)).trans teacher
  exact le_of_pow_le_pow_left₀ (by dsimp only [D];positivity) (inv_nonneg.mpr (pow_nonneg clock.le _)) price

end YM.Integration.WilsonOriginalFullRosterCropFare
end
