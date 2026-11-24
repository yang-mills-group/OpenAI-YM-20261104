import YM.AllOrder.Quay.Native
import YM.Extra.WILSON_STARTUP.Clock
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Quay
open Function Filter Work Tensor Lattice Wilson RG Ovens Finset
open WilsonStartup WilsonStartup.Design WilsonStartup.Start WilsonStartup.Padded Floe Floe.Crest Till Tilt Burn
open PhysicalNext Repeat Pressure ConnectedActivityE6 ConnectedActivityE6.Coat Rosary
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side}
variable {κ j k a c : ℕ}{σ ω' α T C:ℝ}
variable (p:BudgetPoint)(h:Clip)(β:ℝ)
section billing
open Real (exp log)
open RG.Shoot Progress.DirectedRecipe Payments
local notation "M"=>Timing.M
local notation "N"=>Timing.normK
local notation "t"=>p.threshold
-- adjust final Ξ.Payment Costs.
section payment
lemma nearly : ∀ᶠ s in atTop, - M s+2 ≤ -exp ((log s)^2/5) := by
 filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 3] with s h; unfold Timing.M; rw [show exp ((log s)^2)=exp ((log s)^2/5)*exp (4/5*(log s)^2) by rw [← Real.exp_add]; congr 1; ring]; have ht:= Real.add_one_le_exp (4/5*(log s)^2); have hj: 1≤ exp ((log s)^2/5):=Real.one_le_exp (by positivity); nlinarith
lemma kernel_currency {κ' γ:ℝ}(s:ℝ) (hc: - M s+2 ≤ -exp ((log s)^2/5))(hp:1 ≤ κ') (hh: Start.Loan p σ ω' κ' γ) (hm:κ'=M s) (hv:0≤ T)
    (hb: ((p.B+p.B+1:ℕ):ℝ)^4*T ≤ (1:ℝ)/4): Rates p.B (Timing.normK s) (coupon κ' γ) T (κ'-1):= by
 let B:=((p.B+p.B+1:ℕ):ℝ)^4; have h0:1≤ B:= by unfold B; exact one_le_pow₀ (by push_cast; linarith [show 0≤(p.B:ℝ) from Nat.cast_nonneg p.B]) -- maybe
 have hγ : 0 ≤ exp γ-1:=sub_nonneg.mpr (Real.one_le_exp hh.packets.gamma)
 have hi : exp (κ'-1)*coupon κ' γ=(exp 1)⁻¹*(exp γ-1):= by unfold coupon; rw [← mul_assoc, ← Real.exp_add, ← Real.exp_neg (1:ℝ)]; congr 2; ring
 have he: B * inflation (coupon κ' γ) T (κ'-1)≤ 1:=by
    have hx: (exp 1)⁻¹ ≤ (1:ℝ)/2:=by apply (inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ)<1/2)).2; push_cast; linarith [Real.add_one_le_exp (1:ℝ)] -- inv rewrite
    unfold inflation; rw [hi,mul_add,mul_left_comm B _ (exp γ - 1)]; refine le_trans (add_le_add_left (mul_le_mul hx hh.margin (mul_nonneg (by linarith) hγ) (by norm_num)) _) ?_; linarith only [hb] -- add ok? orientation lemma `add_le_add_right`? In Lean add_le_add_left h c outputs c⊕x? tested qu..
 have hx:= he; let w:=inflation (coupon κ' γ) T (κ'-1); have hw:0≤ w:= by unfold w inflation coupon; positivity
 have h0':w≤1:=(le_mul_of_one_le_left hw h0).trans hx
 refine ⟨by linarith [hp],mul_nonneg (Real.exp_pos _).le hγ,hv,le_trans ((le_mul_of_one_le_left hv h0).trans hb) (by norm_num), he,?_⟩
 unfold Bid.quote; refine le_trans (mul_le_mul_of_nonneg_left (sub_le_sub_right (Real.exp_le_exp.mpr h0') _) (Real.exp_pos _).le) ?_; refine le_trans (mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one) (Real.exp_pos _).le) ?_; rw [← Real.exp_add]; unfold Timing.normK; exact Real.exp_le_exp.mpr (by rw [hm]; linarith only [hc]);
end payment
variable (k)
local notation "R"=> ConnectedActivityE6.Rate G Burn.trivialL
lemma voidN : R 1 (fun i:ℝ=>i):= by simpa only [Real.rpow_one] using Burn.tracks G (1:ℝ)
abbrev pricee (G:Gauge)(v l p:ℕ)(β:ℝ):= (2:ℝ)*β*(gold G v l p*Pressure.temp β^(v+5))
lemma prayer (a b:ℕ): R (credit k-1/80) (pricee G (horizon k) a b):= by
 have hx:= ( (voidN (G:=G)|>.mul_left 2).mul (((temp_rate (G:=G)).pow (horizon k+5)).mul_left (gold G (horizon k) a b))); apply Rate.weaken hx; rw [Burn.sale_eq]; push_cast; linarith
abbrev countH (i:ℝ):= ((radiusB i+radiusB i+1:ℕ):ℝ)^4
lemma volumeN : R 0 countH := by unfold countH; push_cast; simpa only [zero_mul] using (((Rate.radius_price (G:=G) (L:=trivialL)).add Rate.radius_price).add (Rate.const 1)).pow 4
abbrev scarf (G:Gauge)(S:RG.Stage)(i:ℝ):ℝ:=  (2:ℝ)*i*(Start.price G S.order S.power*Pressure.temp i^5)
lemma cart (S:Stage): R (-1) (scarf G S):= (( (voidN (G:=G) |>.mul_left 2).mul (((temp_rate (G:=G)).pow 5).mul_left (Start.price G S.order S.power)))).weaken (by norm_num)
abbrev crownE (S:RG.Stage)(i y:ℝ):=costFace (countH i*(y*Real.exp (S.supportExponent+1)))
abbrev scarfE (G:Gauge)(S : RG.Stage)(i:ℝ):=crownE S i (scarf G S i)
lemma cartwork (S:Stage): R (-1) (fun x=> countH x*scarfE G S x):= by
 have h := volumeN (G:=G); refine (h.mul ((h.mul ((cart (G:=G) S).mul_right _)).mul_left _)).weaken (by norm_num)
-- elementary identities.Auction.
lemma tempS {x:ℝ}(hx:0<x): Pressure.temp x=Timing.temp (log x):= by
 unfold Timing.temp Pressure.temp; rw [Real.exp_add,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx,Real.exp_neg]; congr 2; ring
lemma e_all {a:Levels G}{x:ℝ}{n:ℕ}(hz:a.clock.hatBeta n=x)(hx:0<x): a.clock.allowance n=x^(-(11/10):ℝ) ∧ a.clock.forcedAllowance n= Timing.normK (log x):=by
 unfold Timing.normK Calendar.allowance Calendar.forcedAllowance Calendar.hatCoupling Calendar.monitor; rw [hz, Real.sqrt_eq_rpow,← Real.rpow_neg hx.le,← Real.rpow_mul hx.le,← Real.exp_mul]; constructor <;> congr 3 <;> ring
end billing
end YM.AllOrder.Quay
