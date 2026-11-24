import YM.Integration.WilsonOriginalSparseFiledClock
import YM.Integration.WilsonOriginalSparseFiledRanks
import YM.Integration.WilsonCapturedNativeClockFare

/-! At each fixed coupling and angular grade the native clock matrix is a finite
number independent of the side and all regulators. The rooted cut spends part
of its own radius on the exponential width factor of the original tensor fee. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSparseFiledFare
open Finset Lattice Wilson RG Marker QuadraticLocal Multi
open WilsonCapturedClockRankProjection WilsonCapturedPrimaryWindingMaterialRead
open WilsonCapturedSourceAngularRoof WilsonOriginalSparseFiledRanks
open scoped BigOperators Classical

def constant (G:Gauge)(p e r:ℕ):ℝ :=
  (r.factorial:ℝ)⁻¹*charge nativeClock (-(p:ℤ)) (p+e) r (fun i=>|roof G i r 1|)

theorem gross (G:Gauge){V:Type}[DecidableEq V]{Γ:Census V}
    (w:V→ℝ)(s:Hot Γ)(wallet:0<Poly.toll w s.val)
    {σ C H:ℝ}(pos:0<σ)(pc:0≤C)(stock:Real.exp ((min 1 σ)⁻¹^2) ≤ H)
    (p e r:ℕ):
    bill G w s σ C p e r ≤ Real.exp (σ/4)*H*(constant G p e r*C/Poly.toll w s.val):=by
  have hp:0<H:=(Real.exp_pos _).trans_le stock
  let gross:=Real.exp (σ/4)*C*H
  have per (i:ℕ): WilsonCapturedCoveredSourceWage.fare G i r σ C ≤ gross*|roof G i r 1|:=by
    apply (WilsonCapturedNativeClockFare.fare G i r pos pc stock).trans
    calc
      _ = gross*(roof G i r 1) := by dsimp [gross];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_abs_self _) (by dsimp [gross];positivity)
  have bank:charge nativeClock (-(p:ℤ)) (p+e) r (fun j=>WilsonCapturedCoveredSourceWage.fare G j r σ C) ≤
      gross*charge nativeClock (-(p:ℤ)) (p+e) r (fun j=>|roof G j r 1|):=by
    unfold charge
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_left (per i) (norm_nonneg _)
      _ = _ := by ring
  have h:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left bank (inv_nonneg.mpr (Nat.cast_nonneg r.factorial))) wallet.le
  exact h.trans_eq (by unfold constant gross;ring)

theorem cropped {H σ C:ℝ}(pos:0<σ)(reserve:Real.exp ((σ⁻¹)^2) ≤ H)
    (d k:ℕ)(pc:0≤C)(income:C≤H^d)
    (late:(512*((2*(1+d+k):ℕ)+1:ℝ))^2 ≤ Real.log H):
    let m:=Nat.ceil ((Real.log H)^2)/32
    Real.exp (-((σ/8)*(m:ℝ)))*(Real.exp (σ/4)*H*C) ≤ (H^k)⁻¹:=by
  let m:=Nat.ceil ((Real.log H)^2)/32
  let u:=1+d+k
  have hH:0<H:=(Real.exp_pos _).trans_le reserve
  have node:=WilsonOriginalSparseFiledClock.tail pos reserve (2*u) late
  have expo:(H^(2*u))⁻¹=Real.exp (-((2*u:ℕ):ℝ)*Real.log H):=by
    rw [neg_mul,Real.exp_neg,←Real.log_pow,Real.exp_log (pow_pos hH _)]
  rw [expo] at node
  have tested:=Real.exp_le_exp.mp node
  change -(σ/8*(m:ℝ)) ≤ -((2*u:ℕ):ℝ)*Real.log H at tested
  push_cast at tested
  have paid:Real.exp (-(σ/16*(m:ℝ))) ≤ (H^u)⁻¹:=by
    calc
      _ ≤ Real.exp (-((u:ℝ)*Real.log H)) := by apply Real.exp_le_exp.mpr;linarith only [tested]
      _ = _ := by rw [Real.exp_neg,←Real.log_pow,Real.exp_log (pow_pos hH _)]
  have logbig:512^2 ≤ Real.log H:=by
    refine le_trans ?_ late
    apply pow_le_pow_left₀ (by norm_num)
    have :0≤((2*(1+d+k):ℕ):ℝ):=by positivity
    linarith
  have mbig:4 ≤ m:=by
    have ne:=Nat.le_ceil ((Real.log H)^2)
    have lower:(128:ℝ) ≤ (Nat.ceil ((Real.log H)^2):ℝ):=by nlinarith [sq_nonneg (Real.log H-2)]
    have :128 ≤ Nat.ceil ((Real.log H)^2):=by exact_mod_cast lower
    dsimp [m];omega
  have reclaim:Real.exp (-(σ/8*(m:ℝ)))*Real.exp (σ/4) ≤ Real.exp (-(σ/16*(m:ℝ))):=by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have b:4≤(m:ℝ):=by exact_mod_cast mbig
    nlinarith only [mul_nonneg pos.le (sub_nonneg.mpr b)]
  change Real.exp (-(σ/8*(m:ℝ)))*(Real.exp (σ/4)*H*C) ≤ _
  calc
    _ = (Real.exp (-(σ/8*(m:ℝ)))*Real.exp (σ/4))*(H*C) := by ring
    _ ≤ (H^u)⁻¹*(H*H^d) := mul_le_mul (reclaim.trans paid) (mul_le_mul_of_nonneg_left income hH.le) (mul_nonneg hH.le pc) (by positivity)
    _ = _ := by dsimp [u];rw [pow_add,pow_add,pow_one];field_simp

end YM.Integration.WilsonOriginalSparseFiledFare
end
