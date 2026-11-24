import YM.FormalOPE.RG10.Horizon.Crown
/-! # Far estimates determine horizontal projection; no implicit flat-product mask

Quantified at each low horizon and perturbative edition, BEFORE all-order.
Higher horizon can have a different supporting stencil.
Strong estimates on the *response* not just the stored coefficients with nothing to test.
The `Tip` residual has order exactly one more engineering weight with only polynomial-log cost at
fixed perturbative/publication order. The extra positive power ζ appears only when leaving the
finite remainder. This is separated formal geometry; η in exact-action stability, etc independent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Clearing
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD Panel Panel.Consumer InversionTop
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle Arrangements Apertures Transit Route Capture Weave Film
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Ledger Rates
variable {G:Gauge}{F:Frames G}{R:Rails F}{P:Plan F}{Y:Drivers}{Z:Patience P Y}{r m d h n:ℕ}
    (T:Tuned R Z) {E:Fore m} {U:Fin m→ Seats F d}
    {M: Halo} (hM:Valid F h M) {S : Finset (Vantage F)}
    {k:ℕ} (hk:h ≤ k) {V :Vantage F} (hV:V∈ S)
local notation "B" => profit R Z M U E
local notation "Y₁" i:max => (Deck.price F h i:ℝ)

include T hM
lemma repays {α:ℝ}(hα:0<α) (x:Seats F h)(he:∀ᶠ t in atTop,∀ i:Deck F h, coin r (burst R Z (exhibit M i) t E U-imply R Z (exhibit M i) t h x) ≤ tilt t (h+α))
    (i:Deck F h) (j:ℕ) (hj:j≤r): Tendsto (fun t=>coeff j (winter R Z M U E h t i)) atTop (𝓝 (coeff j (x i))) := by
 have hf : 0 < α/2 := by linarith
 let ξ := (h:ℝ)+α-α/2-Y₁ i; have hu: (Y₁ i)≤ h:=by exact_mod_cast Deck.price_bound F h i
 apply tendsto_iff_dist_tendsto_zero.mpr ?_ -- # check
 have hr:=fade_out (show 0 < ξ by unfold ξ; linarith) |>.const_mul (revenue F h)
 rw [mul_zero] at hr
 refine squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) ?_ hr
 filter_upwards [supply T _ hf h r M,he] with s hs ht; rw [dist_eq_norm,← _root_.map_sub]; exact (rstate _ hj).trans (investor T hM hs ht i)

lemma determines {α:ℝ}(hα:0<α) (x:Seats F h)(he:∀ᶠ t in atTop,∀ i:Deck F h, coin r (burst R Z (exhibit M i) t E U-imply R Z (exhibit M i) t h x) ≤ tilt t (h+α))
    (i:Deck F h) (j:ℕ) (hj:j≤r): coeff j (B h i)= coeff j (x i):=by rw [corner]; exact (repays T hM hα x he i j hj).limUnder_eq

omit T hM
include T
private lemma cut_cost (X₁:Vantage F) (j:Deck F k) (n : ℕ) {x : fps} : Polys (fun t=> tilt t (-(Deck.price F k j:ℝ))*coeff n (x * imply R Z X₁ t k (seat j))) := by
 simp_rw [coeff_mul,Finset.mul_sum]; apply Polys.sum; intro i _; simp_rw [mul_left_comm (tilt ..)]; apply Polys.muls (Polys.const _)
 simpa only [tilt,neg_mul_neg] using! journey X₁ T.street T.smooth (T.regular k) i.2 j

def cutBack (A : Seats F k) : Seats F h := A ∘ Deck.climb F hk
local notation "R'" x:max => imply R Z V x k
/-- at least one WHOLE power available by grading the discarded slots, not just ζ. -/
theorem tip (A : Seats F k) (V:Vantage F) (r:ℕ) : ∃ (C:ℝ)(p:ℕ), 0≤C ∧ ∀ t≥(0:ℝ),
    coin r (imply R Z V t k A-imply R Z V t h (cutBack hk A)) ≤ cash t C p (h+1):= by
 let A' := A- promote hk (cutBack hk A); let L:= fun t=> imply R Z V t k
 let I:= @univ (Deck F k) _; let Y(j):=(Deck.price F k j:ℝ)
 let K(j : Deck F k)(t:ℝ):=A' j * L t (seat j)
 have Hu : Polys (fun t=>∑ i:Deck F k, tilt t (-Y i)*coin r (K i t)):= Polys.sum _ _ fun j _=>earn (fun i _=>cut_cost T V j i)
 obtain ⟨b,Z',hu,h0⟩:=Hu
 refine ⟨Z',b,hu,fun t ht=>?_⟩; let X' := fun j=> coin r (K j t)
 have hv(j:Deck F k): X' j ≤ tilt t ((h:ℝ)+1)*(tilt t (-Y j)* coin r (K j t)):= by
   by_cases hh: Deck.price F k j ≤ h
   · obtain ⟨i,rfl⟩:=Deck.of_price F hk hh
     unfold X' K; rw [(show A' (Deck.climb F hk i)=0 from sub_eq_zero.mpr ((proceeds hk (cutBack hk A)).1 i |>.symm)),zero_mul,coin,_root_.map_zero]; simp
   rw [← mul_assoc, ← tilted]; apply le_mul_of_one_le_left (coined _) (le_trans (no_tilt (s:=t)|>.symm.le) (shade ?_ ht))
   have hx : (h:ℝ)+1 ≤ Y j:=by unfold Y; exact_mod_cast Nat.succ_le_of_lt (not_le.mp hh)
   linarith
 have hl : L t A'=∑ j,K j t:= by
   conv_lhs=> rw [seating A', _root_.map_sum]
   simp_rw [map_smul]; rfl
 rw [← same_budget R Z V t (h:=hk),← _root_.map_sub]; change coin r (L t A')≤_; rw [hl]

 apply (coin_fore ..).trans; apply le_trans (sum_le_sum fun j _=> hv j); rw [← Finset.mul_sum]; unfold cash legUp; rw [mul_comm (Z' * _)]
 apply mul_le_mul_of_nonneg_left (le_trans (b:=‖_‖) (Real.le_norm_self _) (h0 t)) tilt_pos.le

lemma transfer_crop (A : Seats F k) {S':Finset (Vantage F)} (r:ℕ) {α:ℝ} (hα: (h:ℝ)< α) (hx : ∀ᶠ t in atTop,∀ u∈ S', coin r (burst R Z u t E U-imply R Z u t k A)≤ tilt t α) : ∃ ζ:ℝ,0<ζ ∧ ∀ᶠ t in atTop,∀ u∈ S', coin r (burst R Z u t E U-imply R Z u t h (cutBack hk A)) ≤ tilt t (h+ζ) := by
 let μ := min α ((h:ℝ)+1/2); let p:= (μ-h)/2; have hp: (h:ℝ)<μ:= lt_min hα (by norm_num); have hf : μ ≤ α:= min_le_left _ _; have h1:μ ≤ (h:ℝ)+1/2:=min_le_right ..
 refine ⟨p,by dsimp [p]; linarith, Filter.eventually_all_finset _|>.2 (fun i hi=>?_)⟩
 obtain ⟨C,b,hC,H⟩:=tip T hk A i r
 filter_upwards [hx, eventually_ge_atTop 0, absorbed (M:=C) (p:=b) (show μ<(h:ℝ)+1 by linarith), clearing_const 2 (show (h:ℝ)+p<μ by unfold p; linarith)] with t ht hp' hs he
 refine (le_of_eq (congr_arg (coin r) (a₂:=burst R Z i t E U-imply R Z i t k A + (imply R Z i t k A-imply R Z i t h (cutBack hk A))) (by abel))).trans ((coin_add ..).trans ?_)
 rw [two_mul] at he; exact le_trans (add_le_add ((ht i hi).trans (shade hf hp')) ((H t hp').trans hs)) he

section horizontal
include hM
-- ATTACHES just at the high frame (! permitted slots & high clocks). Need testing lower lens too.
theorem concord {M': Halo} (hM': Valid F k M')
    (A':Attaches R Z U E r k S) (hu':∀ i:Deck F k,exhibit M' i∈ S) (hc:∀ i: Deck F h,exhibit M i∈ S) : ∀ i (j:ℕ),j≤ r→coeff j (profit R Z M U E h i)=coeff j (profit R Z M' U E k (Deck.climb F hk i)):= by
 obtain ⟨α,hα,hE⟩:=awarded T hM' A' hu'
 let X':=profit R Z M' U E k; have hh : (h:ℝ)≤k:=by exact_mod_cast hk
 obtain ⟨p,hp,H⟩:=transfer_crop T hk X' r (show (h:ℝ)<k+α by linarith) hE
 apply determines T hM hp (cutBack hk X') (r:=r)
 filter_upwards [H] with t ht i using ht (exhibit M i) (hc i)
end horizontal

end YM.FormalOPE.RG10.Clearing
