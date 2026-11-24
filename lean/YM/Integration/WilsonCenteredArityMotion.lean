import YM.Integration.WilsonCenteredCaptureGeometry

/-! Original reporting derivative purse for an arbitrary fixed number of
independently named smooth subwords in the true capture cell. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredArityMotion
open Finset Wilson RG WilsonCenteredLampCapture
open scoped BigOperators Classical

theorem original (p : BudgetPoint) {rad r : ℕ} (near : rad≤p.B) {J : Type} (s : Finset J)
    (load : s.card ≤ r) :
    stage p rad s ≤ (WilsonReportRetainedAnchor.reprice p p.B)^(r+1) :=by
  have count (n : ℕ) : (n:ℝ)+1≤3^(n+1) :=by
    induction n with
    | zero =>norm_num
    | succ n ih =>
      rw [pow_succ (3:ℝ) (n+1)]
      push_cast
      linarith [Nat.cast_nonneg (α:=ℝ) n]
  let X:ℝ:=(1+(rad:ℝ))^p.power
  have X1 : 1≤X :=one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg rad)) 
  have Xpositive : 0≤X :=zero_le_one.trans X1
  have one : X≤X^(r+1) :=by
    simpa only [pow_one] using pow_le_pow_right₀ X1 (Nat.succ_le_succ (Nat.zero_le r))
  have seat : ((s.card+1:ℕ):ℝ)≤3^(r+1) :=(Nat.cast_le.mpr (Nat.succ_le_succ load)).trans (by exact_mod_cast count r)
  have base :=mul_le_mul seat one Xpositive (by positivity : 0≤(3:ℝ)^(r+1))
  rw [←mul_pow] at base
  let pair:= (Finset.univ : Finset (Fin 2))
  have order : stage p rad s ≤(stage p rad pair)^(r+1) :=by
    change (((s.card+1:ℕ):ℝ)*X)^p.order ≤ ((((pair.card+1:ℕ):ℝ)*X)^p.order)^(r+1)
    have slots : ((pair.card+1:ℕ):ℝ)=3 :=by simp [pair]
    rw [slots,←pow_mul,Nat.mul_comm p.order (r+1),pow_mul]
    exact pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) Xpositive) base _
  exact order.trans (pow_le_pow_left₀ (zero_le_one.trans (funded p rad pair))
    (WilsonCenteredCaptureGeometry.motion p near pair (by simp [pair])) _)

end YM.Integration.WilsonCenteredArityMotion
