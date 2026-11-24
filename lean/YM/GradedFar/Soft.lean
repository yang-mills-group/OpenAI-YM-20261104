import YM.GradedFar.Horizon
import YM.GradedFar.Money
/-!
# Analytic remittance for any growing stretch, even though path repeatedly sampled.

Also prices the logarithm for every point of that path, here included ALL upper range.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Neighbor
open Function Filter Set PowerSeries
open Extraction Table Spec OPE.Orbits Climb Trace.Pilot PhysMS
open FVA2 XSpace XSpace.Normalize MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Tide
open FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar
open scoped Topology BigOperators Classical
variable {G:Gauge}
local notation "g" => strength G
variable {hG:G.Simple}
def Wide (G:Gauge)(U B r T:ℝ): Prop:= 1 ≤ T ∧ T ≤ U*(strength G r)^(-B)
variable {U B:ℝ}
include hG
lemma pay_log (hU:0<U)(hB:0<B)(k:ℕ): ∀ᶠ r in trail,
    ∀ T,Wide G U B r T → (1+Real.log T)^k*g r ≤ 1:=by
 filter_upwards [(strength_falls hG).eventually
    (Budget.trade_less hB hU hU (q:=(0:ℝ)) (α:=(1:ℝ)) zero_lt_one 1 zero_le_one k (by simp)),strength_positive hG] with r hr hg T hT
 have hL:=Real.log_nonneg hT.1; have he:= Real.log_le_log (zero_lt_one.trans_le hT.1) hT.2
 specialize hr (U*(g r)^(-B)) ⟨le_rfl,le_rfl⟩
 simp only [Real.rpow_one, Real.rpow_zero, one_mul,mul_one] at hr; rw [mul_comm]; refine le_trans ?_ hr; gcongr
lemma fund_up (hU:0<U)(hB:0<B): ∀ᶠ r in trail, ∀ T,Wide G U B r T →
    0 < g (r*T) ∧ g (r*T) ≤ 2*g r:=by
 filter_upwards [strength_scale hG,out_radius hG (U:=U) (B:=B) _ ( (strength_scale hG).and (strength_positive hG)),
   pay_log (hG:=hG) hU hB 1,strength_positive hG, (Coupling.conforms hG (strength_coupling hG)).eventually_le_const
      (show (0:ℝ)< G.slopeConstant⁻¹/2 from half_pos (inv_pos.mpr (Gauge.slopeConstant_pos hG))), self_mem_nhdsWithin] with
   r hr huv H hg hx (hz:0<r) T hT
 obtain ⟨hs,H'⟩:= huv T hT.1 hT.2; refine ⟨H',?_⟩; specialize H T hT; rw [pow_one] at H;
 have ht:=zero_lt_one.trans_le hT.1; have hm: LogV r-Real.log T = LogV (r*T):= by unfold LogV; rw [Real.log_inv,Real.log_inv, Real.log_mul hz.ne' ht.ne']; ring
 let η:=G.slopeConstant⁻¹; have hh:0<η:= inv_pos.mpr (Gauge.slopeConstant_pos hG)
 have hA: Real.log T * g r^2 ≤ LogV r*g r^2/2:=by rw [hr]; nlinarith [hx,mul_le_mul_of_nonneg_right H hg.le]
 -- exact uniform upper. powers through p via coarse factor 2.
 have hL : η/2 ≤ LogV (r*T) * g r^2:= by rw [← hm]; change G.slopeConstant⁻¹/2 ≤ _; rw [← hr]; linarith only [hA]
 have hZ : 0 < LogV (r*T) := pos_of_mul_pos_left ((half_pos hh).trans_le hL) (sq_nonneg _)
 apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
 apply le_of_mul_le_mul_left _ hZ; unfold η at hh hL
 nlinarith only [hh,hL,hs]
lemma spent (hU:0<U)(hB:0<B)(L N:ℕ): ∀ᶠ p:ℕ in atTop,∀ C:ℝ,0≤C →∀ᶠ r in trail,
    ∀ T, Wide G U B r T → C*T^N*(g r)^p ≤ (g r)^L:=by
 obtain ⟨q,hq⟩:= exists_nat_gt (B*N+L); filter_upwards [eventually_ge_atTop q] with p hp C hC
 obtain H:= (strength_falls hG).eventually (Budget.trade (γ:=(L:ℝ)) (α:=(p:ℝ)) (m:=(0:ℝ)) (q:=(N:ℝ)) hB hU hU C hC 0 (by
    rw [sub_zero]; linarith only [ (show (q:ℝ)≤p by exact_mod_cast hp), hq]))
 filter_upwards [H,strength_positive hG] with r hr hg T hT; specialize hr (U*(g r)^(-B)) ⟨le_rfl,le_rfl⟩; rw [Real.rpow_natCast,Real.rpow_natCast, pow_zero,Real.rpow_natCast,Real.rpow_zero,mul_one,mul_one,mul_right_comm] at hr
 exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hT.1) hT.2 _) hC) (by positivity)).trans hr
-- stronger p-dependent C can always buy. adjust statement.
end YM.Integration.GradedFar.Neighbor
