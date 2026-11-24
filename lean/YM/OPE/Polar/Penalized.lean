import YM.OPE.Polar.Damping
/-! # We can bootstrap on an interior extremum

Scale x variables to clearance before using this. All bounds on closed balls
against REAL displacements, except analyticity qualification. Small fluctuations can
be simultaneous on far and near directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Polar
open Function Filter Set MeasureTheory Metric
open scoped Topology BigOperators Classical
variable {ι X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X] {l:Filter ι}{T N K A:ι→ℝ}

-- y-centered paid ledger
private def tender (f:X→ℂ)(N:ℝ) (x:X) := ‖f x‖* Real.exp (-8*N*‖x‖)
variable {f:X→ℂ}{n k:ℝ}
local notation "D"=>closedBall (0:X) 1
private lemma peak (hn: 1 ≤ n)(h: ∀ x∈ closedBall (0:X) 1, Watches f x n k) (hp:1 ≤ ‖f 0‖) [ProperSpace X] :
    ∃ x∈ D, ‖x‖ < 1/2 ∧ ‖f 0‖ ≤ ‖f x‖ ∧ ∀ y∈ closedBall x (2*n)⁻¹, y∈ D∧ ‖f y‖ ≤ Real.exp 4 * ‖f x‖:=by
    let g:= tender f n; have hc:ContinuousOn f D:=fun x hx=>(h x hx).good.continuousAt.continuousWithinAt; have h0:(0:X)∈ D:= mem_closedBall_self zero_le_one; obtain ⟨x,hx,hg⟩:= (isCompact_closedBall _ _).exists_isMaxOn ⟨0,h0⟩ (show ContinuousOn g D from hc.norm.mul (by fun_prop));
    have hf:g 0=‖f 0‖:=by simp [g,tender]
    have hu : (g x) ≤ ‖f x‖:= mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (by have hz:= norm_nonneg x; nlinarith only [hn,hz]))
    have hG: ‖x‖ < 1/2:=by
       by_contra! he; have hz := mul_le_mul_of_nonneg_right (h x hx|>.origin) (Real.exp_nonneg (-8*n*‖x‖))
       have he' : n+(-8*n*‖x‖)<0:=by nlinarith only [hn,he]
       have hh : g x<1:= hz.trans_lt (show Real.exp n*Real.exp (-8*n*‖x‖) < 1 by rw [← Real.exp_add]; exact Real.exp_lt_one_iff.mpr he')
       exact hh.not_ge (hp.trans (hf.symm ▸ hg h0))
    refine ⟨x,hx,hG,le_trans (hf ▸ hg h0) hu,fun y hy=> ?_⟩; have ht:0 < 2*n:=mul_pos two_pos (zero_lt_one.trans_le hn);
    have he: ‖y‖ - ‖x‖ ≤ (2*n)⁻¹ := le_trans (norm_sub_norm_le ..) ((dist_eq_norm y x) ▸ mem_closedBall.mp hy)
    have hh: y ∈ D:= mem_closedBall_zero_iff.mpr (by rw [← one_div (2*n)] at he; have hz : 1/(2*n) ≤ 1/2:= (div_le_div_of_nonneg_left zero_le_one two_pos (by linarith)); linarith)
    refine ⟨hh,?_⟩; let y' (z:X):= Real.exp (-8*n * ‖z‖); have hx:4+(-8*n*‖y‖) ≥ -8*n*‖x‖:= by
       have he:= mul_le_mul_of_nonneg_left he ht.le; rw [mul_inv_cancel₀ ht.ne'] at he; nlinarith only [he]
    refine (mul_le_mul_iff_left₀ (Real.exp_pos (-8*n*‖y‖))).mp (le_trans (show ‖f y‖*(y' y) ≤‖f x‖*(y' x) from hg hh) ?_); rw [mul_comm (Real.exp 4),mul_assoc,← Real.exp_add]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone hx) (norm_nonneg _)

def freeZone (n k:ℝ):= k*(4*Real.exp 4*Real.exp 4*n^2)
lemma minBound (hn : 1 ≤ n)(hk: 1 ≤ k) : 4*n ≤ freeZone n k:= by
    unfold freeZone; have he : 1 ≤ Real.exp 4:= Real.one_le_exp (by norm_num); have hh:= le_mul_of_one_le_left (show 0 ≤ 4*Real.exp 4*Real.exp 4*n^2 by positivity) hk
    apply le_trans _ hh; nlinarith only [hn,he,mul_le_mul_of_nonneg_left he (show 0≤Real.exp 4 from Real.exp_nonneg _), mul_le_mul_of_nonneg_right (one_le_mul_of_one_le_of_one_le he he) (sq_nonneg n)]
private lemma touch {x y:X} (hx : ‖x‖ < (1/2:ℝ))(hn:1 ≤ n)(hk:1≤k)(h:∀ x∈ closedBall (0:X) 1, Watches f x n k)(hp:1 ≤ ‖f x‖)(ht:∀ y∈ closedBall x (2*n)⁻¹, y∈ closedBall (0:X) 1 ∧ ‖f y‖ ≤ Real.exp 4 * ‖f x‖)(he:‖y-x‖ ≤ (2*freeZone n k)⁻¹) : ‖f x‖ ≤ 2*‖f y‖:=by
    let a:= freeZone n k; let b:=(4*n)⁻¹; let Z:= closedBall x b; have hf:0<n:=zero_lt_one.trans_le hn; have hq:4*n≤a:= minBound hn hk; have hv:0<a:= (show 0<4*n by positivity).trans_le hq; have ha:0<b:= by unfold b; positivity
    have hu:b+b=(2*n)⁻¹:= by unfold b; field_simp <;> ring
    have he':‖y-x‖ ≤ b:= he.trans (inv_anti₀ (by positivity) (by change _ ≤ 2*a; linarith only [hv,hq])); let v:= a*‖f x‖
    have hH(u)(hU:u∈Z) : closedBall u b⊆ closedBall x (2*n)⁻¹:=by
       refine closedBall_subset_closedBall' ?_; linarith only [show dist u x ≤ b from hU,hu] -- order?
    have hP(u)(hU:u∈ Z):Watches f u n k:= h _ (ht _ (hH u hU (mem_closedBall_self ha.le))).1
    have hJ(u)(hU:u∈ Z) : ‖fderiv ℝ f u‖ ≤ v:=by
       apply ((hP u hU).paid hn (one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hp) (fun v hv=> (ht _ (hH u hU hv)).2)).trans_eq; unfold v a freeZone; ring
    have he:= (convex_closedBall x b).norm_image_sub_le_of_norm_fderiv_le (fun x hx=> (hP x hx).good) hJ (mem_closedBall_self ha.le) (show y∈Z from (by unfold Z; rwa [mem_closedBall,dist_eq_norm]));
    have hε:‖f y - f x‖ ≤ ‖f x‖/2:=by
       refine he.trans ((mul_le_mul_of_nonneg_left (show ‖y-x‖ ≤ (2*a)⁻¹ from ?_) (mul_nonneg hv.le (norm_nonneg _))).trans_eq (?_)); assumption; field_simp
    linarith only [hε, norm_sub_norm_le (f x) (f y), norm_sub_rev (f x) (f y)]
-- field_simp promotes v* etc

variable [ProperSpace X]
-- user chooses sample curve in a tiny mesh distance, may depend on maximizing point. Lipschitz weights and damping protect against all samples.
lemma price_mesh {F:ι→ X→ℂ}(ht:Tendsto T l atTop)
    (hn:∀ᶠ i in l,1 ≤ N i) (hk:∀ᶠ i in l,1 ≤ K i)
    (h:∀ᶠ i in l,∀ x∈ closedBall (0:X) 1, Watches (F i) x (N i) (K i)) (hx:∀ x:ι → X, (∀ᶠ i in l, ‖x i‖≤1/2) → ∃ y:ι→ X, Wallet l T (fun i=> F i (y i)) ∧ ∀ᶠ i in l,‖y i-x i‖ ≤ (2*freeZone (N i) (K i))⁻¹) : Wallet l T (fun i=> F i 0):=by
    let p(i):= (1 ≤ ‖F i 0‖) ∧ 1 ≤ N i ∧ 1≤ K i ∧ ∀ x∈ closedBall (0:X) 1, Watches (F i) x (N i) (K i)
    let x i:= if h:p i then Classical.choose (peak h.2.1 h.2.2.2 h.1) else 0; obtain ⟨y,hy,h0⟩:= hx x (by
       filter_upwards with i; unfold x; split; next h=>exact le_of_lt (Classical.choose_spec (peak h.2.1 h.2.2.2 h.1)).2.1
       norm_num)
    apply ((Wallet.const ht (1:ℝ)).add ht ((Wallet.const ht (2:ℝ)).mul hy.norm)).of_est; filter_upwards [h,h0,hn,hk] with i hi hv hn hk; by_cases he:1 ≤ ‖F i 0‖
    · have hu:p i:= ⟨he,hn,hk,hi⟩; let y':= x i; have hg:= Classical.choose_spec (peak hn hi he); rw [show Classical.choose (peak hn hi he)=x i from by unfold x; rw [dif_pos hu]] at hg; linarith only [hg.2.2.1, touch (x:=x i) hg.2.1 hn hk hi (he.trans hg.2.2.1) hg.2.2.2 hv ]
    linarith only [norm_nonneg (F i (y i)), lt_of_not_ge he]
end YM.OPE.Polar
