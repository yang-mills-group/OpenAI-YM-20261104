import YM.FormalOPE.RG10.Horizon.Distill

/-! # Quantitative dyadic argument (ratio exp 1 OK) -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Clearing
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD Panel Panel.Consumer InversionTop
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle Arrangements Apertures Transit Route Capture Weave Film
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Ledger Rates
variable {G:Gauge}{F:Frames G}{R:Rails F}{P:Plan F}{Y:Drivers}{Z:Patience P Y} {m r h d:ℕ}
  {f:ℝ→ ℝ}{α M:ℝ}
section disc
variable (hM:0 ≤ M)(hu:0<α)
    (he : ∀ᶠ s in atTop, ∀ t∈Set.Icc s (s+1),dist (f s) (f t) ≤ M * tilt s α)
include hu hM he

theorem shadows : ∃ K:ℝ,0 ≤ K ∧ ∀ᶠ s in atTop, ∀ t≥s, dist (f s) (f t)≤ K*tilt s α := by
 obtain ⟨s,h₁⟩:=Filter.eventually_atTop.mp he; have hh:0 < 1-tilt 1 α:= sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith only [hu]))
 let b:= M/(1-tilt 1 α); have hB:0 ≤ b:=div_nonneg hM hh.le
 refine ⟨b+M,by positivity,?_ ⟩;
 filter_upwards [eventually_ge_atTop s] with t ht u huu; have hl (n:ℕ) : s ≤ t+n:= le_trans ht (le_add_of_nonneg_right (by positivity)); have hc(n:ℕ): tilt (t+n+1) α=tilt (t+n) α*tilt 1 α:= duration
 have hb : b*(1-tilt 1 α) = M:= div_mul_cancel₀ _ hh.ne'
 have hr(n:ℕ): dist (f t) (f (t+n)) ≤ b*(tilt t α- tilt (t+n) α):= by
   induction n with
   | zero=> simp
   | succ n ih=>
     rw [Nat.cast_add_one,← add_assoc]; apply (dist_triangle (f t) (f (t+n)) _).trans; apply (add_le_add ih (h₁ _ (hl n) _ (Set.right_mem_Icc.mpr (show t+n ≤ t+n+1 by linarith)))).trans;
     rw [hc,← hb]; apply le_of_eq; ring
 let n:= Nat.floor (u-t); have hP:=h₁ (t+n) (hl _) u (by
   have ht:↑n ≤ u-t:=Nat.floor_le (by linarith)
   exact ⟨by linarith, by linarith [Nat.lt_floor_add_one (u-t)]⟩)
 have hE: tilt (t+n) α≤ tilt t α:= cooling (le_add_of_nonneg_right (by positivity)) hu.le
 exact (dist_triangle _ (f (t+n)) _).trans ((add_le_add (hr n) hP).trans (by nlinarith only [mul_nonneg hB (tilt_pos (ξ:=α) (s:=t+n) |>.le), mul_le_mul_of_nonneg_left hE hM]))

theorem forecasts : ∃ a:ℝ,Tendsto f atTop (𝓝 a)∧ ∃ K:ℝ,0 ≤ K ∧ ∀ᶠ s in atTop,dist (f s) a ≤ K*tilt s α:= by
 obtain ⟨K,hk,H⟩:= shadows hM hu he;
 have ht : CauchySeq f:= by
   refine Metric.cauchySeq_iff'.2 (fun ε hε => ?_)
   obtain ⟨s,he,hv⟩:= (H.and (((fade_out hu).const_mul K).eventually (gt_mem_nhds (a:=ε) (by simpa using hε)))).exists
   exact ⟨s,fun n hn=> by rw [dist_comm]; exact lt_of_le_of_lt (he n hn) hv⟩
 obtain ⟨a,ha⟩:= cauchySeq_tendsto_of_complete ht -- scope
 refine ⟨a,ha,K,hk,?_⟩; filter_upwards [H] with s hs; exact le_of_tendsto (tendsto_const_nhds.dist ha) ((eventually_ge_atTop s).mono hs)
end disc

variable (T:Tuned R Z) {M₀: Halo} (hM :Valid F h M₀){S:Finset (Vantage F)} {x:Fin m→ Seats F d} {E:Fore m}
  (A: Attaches R Z x E r h S)(hC:∀ i:Deck F h,exhibit M₀ i∈ S)
include A T hM hC
local notation "v" => winter R Z M₀ x E h

theorem payments : ∃ α:ℝ,0<α ∧ ∀ (j : Deck F h),∀ i ≤ r,∃ b:ℝ,Tendsto (fun t=>coeff i (v t j)) atTop (𝓝 b) ∧ ∃ C:ℝ,0 ≤ C ∧
     ∀ᶠ t in atTop, ‖coeff i (v t j)-b‖ ≤ C* tilt t (h+α-(Deck.price F h j:ℝ)) := by
 obtain ⟨α,hα,H⟩:= linkedin T hM A hC; refine ⟨α,hα,fun j i hi=>?_⟩;
 apply forecasts (M:=2*revenue F h) (by unfold revenue; positivity) (by
   have hx : (Deck.price F h j:ℝ) ≤ h:= by exact_mod_cast Deck.price_bound F h j
   linarith)
 filter_upwards [H] with s hs t ht; change ‖coeff i (v s j)-coeff i (v t j)‖≤_; rw [← _root_.map_sub]; exact (rstate _ hi).trans (hs _ ht _)
end YM.FormalOPE.RG10.Clearing
