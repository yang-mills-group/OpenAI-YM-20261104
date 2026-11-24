import YM.Integration.WilsonOriginalSparseFiledFare
import YM.Integration.WilsonOriginalSparseFiledRanks
import YM.Integration.WilsonCapturedNativeClockFare

/-! At each fixed coupling and angular grade the native clock matrix is a finite
number independent of the side and all regulators. The rooted cut spends part
of its own radius on the exponential width factor of the original tensor fee. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSparseFiledPostPrice
open Finset Lattice Wilson RG Marker QuadraticLocal Multi
open WilsonCapturedClockRankProjection WilsonCapturedPrimaryWindingMaterialRead
open WilsonCapturedSourceAngularRoof WilsonOriginalSparseFiledRanks
open scoped BigOperators Classical


open WilsonOriginalSparseFiledFare

theorem nonnegative (G:Gauge)(p e r:ℕ):0≤constant G p e r:=by
  unfold constant WilsonCapturedClockRankProjection.charge
  positivity

theorem paid (G:Gauge){V:Type}[DecidableEq V]{Γ:Census V}
    (w:V→ℝ)(s:Hot Γ)(wallet:0<Poly.toll w s.val)
    {σ C H:ℝ}(pos:0<σ)(pc:0≤C)(reserve:Real.exp ((σ⁻¹)^2) ≤ H)
    (hot:Real.exp 1 ≤ H)(p e r d k:ℕ)
    (income:2*(constant G p e r*C/Poly.toll w s.val) ≤ H^d)
    (late:(512*((2*(1+d+k):ℕ)+1:ℝ))^2 ≤ Real.log H):
    let m:=Nat.ceil ((Real.log H)^2)/32
    Real.exp (-((σ/8)*(m:ℝ)))*(2*bill G w s σ C p e r) ≤ (H^k)⁻¹:=by
  have stock:Real.exp ((min 1 σ)⁻¹^2) ≤ H:=by
    by_cases small:σ ≤ 1
    · simpa only [min_eq_right small] using reserve
    · simpa only [min_eq_left (le_of_not_ge small),inv_one,one_pow] using hot
  have W:=WilsonOriginalSparseFiledFare.gross G w s wallet pos pc stock p e r
  let A:=constant G p e r*C/Poly.toll w s.val
  have zero:0≤2*A:=mul_nonneg (by norm_num) (div_nonneg (mul_nonneg (nonnegative G p e r) pc) wallet.le)
  change _*(2*bill G w s σ C p e r) ≤ _
  apply le_trans _ (WilsonOriginalSparseFiledFare.cropped pos reserve d k zero income late)
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  calc
    _ ≤ 2*(Real.exp (σ/4)*H*A) := mul_le_mul_of_nonneg_left W (by norm_num)
    _ = _ := by ring

end YM.Integration.WilsonOriginalSparseFiledPostPrice
end
