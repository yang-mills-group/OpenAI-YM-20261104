import YM.AllOrder.Gyro.Lacuna
import YM.Pert.Kinetic.Ebb
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Gyro
open Function Filter Lattice RG Wilson Push Push.AbsoluteSums Precision AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration PhysicalNext MeasureTheory Finset
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m:Side}{p:BudgetPoint}(d:RegularAddress n){f:Config G n→ℝ}(g:G.Simple)(H:p.Regular d.support f) (x y:Site n) (b:PlaqAxes)
section period
variable {c:ℝ}(h:p.supBounds d.site d.support f c)
include h H g
omit h H in
lemma esc_bound (t:BudgetPoint) (o x:Site n):t.dirBound o (t.threshold • (esc G b x)):= by
 intro e; rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg t.threshold_pos.le]; apply mul_le_mul_of_nonneg_left _ t.threshold_pos.le; unfold esc; split; · rw [spike_norm g]; exact one_le_pow₀ (by simp)
 rw [norm_zero]; positivity
lemma sale : |logHessian f (esc G b x) (esc G b y)| ≤ c*(3/p.threshold^2):= by
 let r:=esc (n:=n) G b; have hp:=p.threshold_pos; have he(z:Site n) : (1/p.threshold)⁻¹ • r z=p.threshold • r z:=by simp
 have hh:=Pert.Kinetic.scaled_price g H h (r x) (r y) (r:=1) (t:=1) zero_lt_one zero_lt_one ((he x).symm ▸ esc_bound g b p d.site x) ((he y).symm ▸ esc_bound g b p d.site y); exact hh.trans_eq (by ring)
variable (n) in
def reward (t:ℝ):ℝ:= (3/t^2)*(n.val:ℝ)^10
omit h H g in
lemma rev (t:BudgetPoint)(n:Side) : 0 ≤ reward n t.threshold:=by unfold reward; have hh:= t.threshold_pos; positivity
lemma script : |meter f b| ≤ c*reward n p.threshold:= by
 have hu:= h.1; have hj:= p.threshold_pos; have hh :∀ x y:Site n,|coord x y b.val.1 ^2* logHessian f (esc G b x) (esc G b y)| ≤ (n.val:ℝ)^2*(c*(3/p.threshold^2)):=by
    intro x y; rw [abs_mul,abs_of_nonneg (sq_nonneg _), ←sq_abs]; apply mul_le_mul _ (sale _ g H _ _ b h) (abs_nonneg _) (by positivity); gcongr; exact highest ..
 unfold meter; rw [abs_div,abs_neg,div_le_iff₀ (by norm_num : (0:ℝ)< |2|),abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
 refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun x _=> (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _=> hh x y))).trans ?_); simp only [Finset.sum_const,Finset.card_univ, nsmul_eq_mul,site_card]; push_cast; unfold reward; have ht:0≤ c* (3/p.threshold^2)*(n.val:ℝ)^10:=by positivity
 linarith only [ht]
-- E of both Early Colon expressions, no wrap cancellations demand, support can actually pay newly chosen wrap at nearly same rated exponent.
omit H h
open Push.AbsoluteSums.Footprint Averaging
local notation "a"=> axes01
local notation "∆"=>Averaging.delta
variable {X : Listing G n}{v:Source G n}{c w τ:ℝ} (he:Collection.Local X p v c w) (h0:20<n.val)
def vault (n:Side)(p:BudgetPoint)(c:ℝ):= c*Real.exp (-preExponent p*pitch n p.B)
-- normalized at each anchor? Averaging over torus on signed; may expense Vol only. Estimate |
include he
local notation "q"=>X.read v
variable {f' : ℕ→ℝ}
local notation "𝓗"=> logHessian
set_option quotPrecheck false
local notation "i★" => (fun i:ℕ => X.reg i|>.site)
lemma scorebill (b:PlaqAxes)(x y:Site n): Summable fun i=> 𝓗 (v.logRead i) (esc G b x) (esc G b y):= by
 obtain ⟨u,hu,hV⟩:= (q).E_total he.unweighted; exact Summable.of_norm_bounded (hu.mul_right (3/p.threshold^2)) (fun i=> sale _ g (he.smooth i) _ _ b (hV i))
lemma mindset(b:PlaqAxes) : Summable fun i=>meter (v.logRead i) b:= by
 obtain ⟨u,hu,hV⟩:= (q).E_total he.unweighted; exact Summable.of_norm_bounded (hu.mul_right (reward n p.threshold)) (fun i=> script _ g (he.smooth i) b (hV i))
include h0
lemma headline_p (hm:∀ i,p.supBounds (i★ i) (X.reg i|>.support) (v.logRead i) (f' i)) (hf:Quotes.early p X.reg f' c) : ∀ x:Site n,|(∑' i, if (X.reg i).site=x then projection (X.reg i) (v.logRead i) a a-meter (v.logRead i) a else 0)| ≤ reward n p.threshold *vault n p c:= by
 intro x; let T:= reward n p.threshold; let r := X.reg; let q' i:= if i★ i=x then projection (X.reg i) (v.logRead i) a a-meter (v.logRead i) a else 0; let f₀ i := if i★ i=x then f' i *Real.exp (preExponent p*coverNumber p.B (r i).support) else 0
 let V:=Real.exp (-preExponent p*pitch n p.B); have hv:0≤V:=(Real.exp_pos _).le; have ht:0≤T:= rev p n; -- fix rev signature
 have hh : SumBudget f₀ c:= hf x; have hc : SumBudget (fun i=> (T*V)*f₀ i) ((T*V)*c):= budget_scale (mul_nonneg ht hv) hh; have hk:= hc.2.1
 have he i : ‖q' i‖ ≤ T*V*f₀ i:= by
    dsimp only [q',f₀,r]; split; swap; · rw [norm_zero,mul_zero]
    rename_i he; by_cases hn:Nonwrapping (expand (r i)) (i★ i); · rw [projection, if_pos hn, reads _ g (‹Collection.Local X p v c w›.smooth i) a (by omega) fun x hx=> hn x (Finset.mem_union_left _ hx),sub_self,norm_zero]; have hq:= hc.1 i; dsimp only at hq; rwa [show f₀ i= _ from (show f₀ i=f' i * Real.exp _ from if_pos he)] at hq
    rw [projection,if_neg hn,zero_sub,norm_neg]; refine (script _ g (‹Collection.Local X p v c w›.smooth i) a (hm i)).trans ?_
    change f' i*T ≤ _; rw [mul_mul_mul_comm,mul_comm]; refine le_mul_of_one_le_right (mul_nonneg ht (hm i|>.1)) ?_ -- ordering?
    unfold V; rw [← Real.exp_add]; refine Real.one_le_exp ?_; rw [neg_mul]; change 0 ≤ -(preExponent p*(pitch n p.B)) + preExponent p * coverNumber p.B (r i|>.support); linarith only [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ)|>.mpr (adjudicate p.B h0 (d:=r i) hn)) (show 0 ≤ preExponent p from by unfold preExponent; linarith [p.exponent_pos])]
 let H₁:=hk.of_nonneg_of_le (fun i=> norm_nonneg _) he; have hv₁ : T*V*c=T*vault n p c:= by unfold vault V;ring
 exact (norm_tsum_le_tsum_norm H₁).trans ((H₁.tsum_le_tsum he hk).trans (hc.2.2.trans_eq hv₁))
end period
end YM.AllOrder.Gyro
