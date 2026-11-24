import YM.LocalLTE.Concert.Cushion
import YM.LocalLTE.MarkPT.Motes
/-!
# Numerical reading of CONDITIONAL LOG/value, in the physical theory. On all passing V (incl flagged not all? only those with *no flags* for this corollary*. Always keep global densities with actual gas).

Intrinsic statement is supported norm. Here reduce to output value prices for source probes (no cheap extensive/corner reading without this step).
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Set Lattice Wilson RG Overlay Marker Finset MeasureTheory
open Work.H03 Extra.Trajectories Progress.DirectedRecipe Layers Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side} {P:Rep G n}
variable {V:Type}[DecidableEq V][Fintype V] {R:Census V} (A B D:Overlay.Bands R P)(t:V→ℝ)
variable (U:Config G n) {a b c d e f A' B' x y s:ℝ}
local notation "pv"=> Poly.price t
open Overlay
lemma beaconY (P:Poly R)(x t σ:ℝ) (K:ℕ)(hx:1≤x)(ht:0 ≤t)(hs:Fintype.card V ≤ K) {b r:ℝ} (he:σ≥0)(hp:Poly.price (fun _=> PhysicalNext.Repeat.Mallow.neat x t) P ≤ σ*b) (h: x^((t+2)*K)*b ≤ r): Poly.price (fun _=>1) P ≤ σ*r:=by
    let u:V→ℝ:=fun _=> PhysicalNext.Repeat.Mallow.neat x t; let κ:= x^(t+2); let k:=κ^K; have ho:1 ≤κ:= Real.one_le_rpow hx (by positivity); have h0:0 ≤ k:=pow_nonneg (zero_le_one.trans ho) _
    have hα (i:R.Mode):Poly.toll (fun _=> (1:ℝ)) i ≤ k*Poly.toll u i:=by
       have hf(i): (1:ℝ) ≤ κ*u i:= le_of_eq (by unfold u κ PhysicalNext.Repeat.Mallow.neat; rw [← Real.rpow_add (by positivity),show t+2+(-t-2)=0 by abel, Real.rpow_zero]) -- unfold
       apply le_trans (prod_le_prod (s:=i.val) (fun _ _=>zero_le_one) (fun i _=>hf i)) _; rw [prod_mul_distrib,prod_const]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ho ((card_le_univ _).trans hs)) (Poly.worth (fun _=>Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _) _).le -- check order.
    apply le_trans (b:=k*Poly.price u P) _ ((mul_le_mul_of_nonneg_left hp h0).trans _)
    · unfold Poly.price; rw [mul_sum]; refine sum_le_sum fun i _=>?_; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (hα i) (norm_nonneg _)
    rw [mul_left_comm k σ]; apply mul_le_mul_of_nonneg_left _ he; unfold k κ; rw [← Real.rpow_mul_natCast (by positivity)]; exact h
end YM.LocalLTE.Port
