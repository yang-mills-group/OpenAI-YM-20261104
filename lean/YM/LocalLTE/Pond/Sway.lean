import YM.LocalLTE.Pond.Troops
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes
variable {G}
open Extra.Iteration Urns
open Time
variable (G) (L:Side)(Q:Stage)(u:ℝ){a b:ℝ}{m:ℕ}(hc:Price.Penny m a b Q G)
local notation "p"=> (Time.probe Q)
local notation "H"=>tH (Time.probe Q)
local notation "¥"=> Time.base G Q
local notation "ℱ"=> (fun x=>betaF G x L)
-- purchase y comparison. hc pre.Commit t≥ growth last. α abs ≤ K (D fixed after L). small forecast bail.
lemma calm (a:ℝ): ∀ᶠ t in atTop,∀ (P:BudgetPoint),P.threshold=Pressure.temp t→ (a*(betaF G t L)^(chip 0)) ≤ P.threshold^2 :=by
   have he:= Rate.mul ((Rate.power (G:=G) (L:=L) (a:=chip 0)).mul_left a) (Price.curveT G L)
   filter_upwards [he.below (by norm_num [chip]) 1 zero_lt_one] with t hx P hP
   have hz: a*betaF G t L^(chip 0)*(Pressure.temp t^ (2:ℕ))⁻¹ ≤ 1:= (le_abs_self _).trans hx; rw [← hP, ← div_eq_mul_inv] at hz; exact div_le_one₀ (sq_pos_of_pos P.threshold_pos)|>.1 hz
include hc
lemma pay_bare : ∀ᶠ t in atTop,∀ (P:BudgetPoint), Time.Same Q P→P.threshold ≤ 2*Pressure.fiery G t L→∀ α:ℝ,|α|≤|u|→
     Price.tH P * regularNeed G P Q.clip Q.width Q.paths α (a*(betaF G t L)^(chip 0)) ≤ b*(betaF G t L)^(chip 0):= by
    let d:=(1+tH p)*(1+Time.base G Q)*a
    have hv:=hc.1; have he:= (Time.base_nonneg G Q); have hp₀:0<H:=Real.exp_pos _; have hh := (Time.base_nonneg G Q).1; have hd:0<d:=by unfold d; positivity
    let g t:=H*(Time.top G Q*(|u| * (2*Pressure.fiery G t L)^3)); have hg:Rate G L (-(3/2)) g:= by
       have hh:= (((((Rate.flame (G:=G) (L:=L)).mul_left 2).pow 3).mul_left |u|).mul_left (Time.top G Q)).mul_left H; norm_num at hh; exact hh -- edit
    filter_upwards [Sienna.contraction G L (a:=1) hd hg (by norm_num [chip]:-(3/2:ℝ)<chip 0), Delay.shift_pos G L] with t ht hB P hP hT α hα
    have hu:tH P*(Time.top G Q*(|α| * P.threshold^3)) ≤ g t:= by rw [show tH P=tH p from (Price.validS G Q hP).2.1]; have hp:=P.threshold_pos; unfold g; gcongr; exact he.2
    rw [Time.table G Q hP]
    rw [mul_add]; refine le_trans (add_le_add_right hu _) ?_; rw [show Price.tH P=tH (Time.probe Q) from (Price.validS G Q hP).2.1]; let S:= (betaF G t L)^(chip 0); rw [one_mul] at ht; have hx:8*d ≤ b := by unfold d; have HZ : 8*(1+tH p)*(1+Time.base G Q)*a ≤ b:=hc.2.2.2.1; linarith only [HZ]
    have hp : (H)*(¥)*a ≤ d:= by unfold d; nlinarith only [hp₀, he.1,hv, mul_nonneg hv.le he.1, mul_pos hv hp₀]
    have he:0<S:=Real.rpow_pos_of_pos hB _; linarith only [ht,mul_pos hd he,mul_le_mul_of_nonneg_right hp he.le,mul_le_mul_of_nonneg_right hx he.le]
-- ∆ reserve. soft reset scaling. cost spare.
lemma pay_force : ∀ᶠ t in atTop, ∀ (P:BudgetPoint), Time.Same Q P→P.threshold=Pressure.temp t → P.threshold ≤ 2*Pressure.fiery G t L→ P.B = Pressure.radiusB t →
    ∀ (Δ α:ℝ),P.threshold^2*|Δ| ≤ a*(betaF G t L)^(chip 0) → |α| ≤ |u| → Price.lofty P G Q.width Q.paths α Δ ≤ a*(betaF G t L)^(chip 0):=by
    let σ:=Q.width; let C:=Q.paths; let A(x:ℝ):= (((ballCost (2*Pressure.radiusB x):ℝ))* (2*(turnFee p*((|u|+1)*(2*Pressure.fiery G x L)^3))*highBase G p σ C))*Real.exp ((Q.supportExponent+1)*ballCost 2)
    have hr:Rate G L (-(3/2)) A:=by
       have he:Rate G L 0 (fun x=> (ballCost (2*Pressure.radiusB x):ℝ)):= by simpa only [Nat.add_zero] using Census.width_rate G L 2 0
       have ht: Rate G L (-(3/2)) (fun x=> 2*(turnFee p*((|u|+1)*(2*Pressure.fiery G x L)^3))*highBase G p σ C):= by
          have hh:= ((((((Rate.flame (G:=G) (L:=L)).mul_left 2).pow 3).mul_left (|u|+1)).mul_left (turnFee p)).mul_left 2).mul_right (highBase G p σ C); convert hh using 1; norm_num
       exact ((he.mul ht|>.weaken (by linarith)).mul_right _)
    filter_upwards [Price.calm G L a,Sienna.contraction G L (a:=1) hc.1 hr (by norm_num [chip]: -(3/2:ℝ)<chip 0)] with t ht hv P hP h hB hR Δ α hΔ hα
    have he:=Price.validS G Q hP -- edit
    have ht : |Δ| ≤1:= by apply le_of_mul_le_mul_left _ (sq_pos_of_pos P.threshold_pos); rw [mul_one]; exact hΔ.trans (ht P h)
    have hz:|α+Δ| ≤ |u| + 1:=(abs_add_le ..).trans (add_le_add hα ht); rw [one_mul] at hv
    refine le_trans ?_ hv.le; unfold Price.lofty A; rw [he.1, he.2.2.2.1, hP.2.2,hR]; have hx:=turnFee_pos p; have hp':=P.threshold_pos; have hh:= (budget_pos p G Q.clip Q.width_pos Q.paths_pos.le).2.1
    gcongr
end YM.AnalyticBridge.VerifiedReset.Collection.Price
