import YM.RG17.Censor
import YM.OPE.Log.Snap
/-! hike to precision from pay at mesh. From Penalized; retains precise grid price (NOT wallet increase). -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Polar.Joint17
open Function Filter Set MeasureTheory Metric RG17
open scoped Topology BigOperators Classical
variable {ι X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X] {l:Filter ι}{T N K A:ι→ℝ}
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

lemma hike {F:ι→ X→ℂ} [ProperSpace X]
    (hn:∀ᶠ i in l,1 ≤ N i) (hk:∀ᶠ i in l,1 ≤ K i)
    (h:∀ᶠ i in l,∀ x∈ closedBall (0:X) 1, Watches (F i) x (N i) (K i)) (hx:∀ x:ι → X, (∀ᶠ i in l, ‖x i‖≤1/2) → ∃ (C:ℝ) (y:ι→ X), (∀ᶠ i in l, ‖F i (y i)‖ ≤ C) ∧ ∀ᶠ i in l,‖y i-x i‖ ≤ (2*freeZone (N i) (K i))⁻¹) : ∃ C:ℝ, ∀ᶠ i in l, ‖F i 0‖ ≤ C:=by
    let p(i):= (1 ≤ ‖F i 0‖) ∧ 1 ≤ N i ∧ 1≤ K i ∧ ∀ x∈ closedBall (0:X) 1, Watches (F i) x (N i) (K i)
    let x i:= if h:p i then Classical.choose (peak h.2.1 h.2.2.2 h.1) else 0; obtain ⟨C,y,hy,h0⟩:= hx x (by
       filter_upwards with i; unfold x; split; next h=>exact le_of_lt (Classical.choose_spec (peak h.2.1 h.2.2.2 h.1)).2.1
       norm_num)
    refine ⟨max (2*C) 1,?_⟩; filter_upwards [h,h0,hn,hk,hy] with i hi hv hn hk hy; by_cases he:1 ≤ ‖F i 0‖
    · have hu:p i:= ⟨he,hn,hk,hi⟩; have hg:= Classical.choose_spec (peak hn hi he); rw [show Classical.choose (peak hn hi he)=x i from by unfold x; rw [dif_pos hu]] at hg; exact le_trans (show _≤2*C from by linarith only [hy,hg.2.2.1,touch (x:=x i) hg.2.1 hn hk hi (he.trans hg.2.2.1) hg.2.2.2 hv]) (le_max_left ..)
    exact le_trans (le_of_not_ge he) (le_max_right ..)
open RG17 Lattice PhysicalNext.Repeat.Legato Filter
variable {G:Gauge}{C:Family G}{m:ℕ}{L: Filter ℝ}{M: ℝ}(hz:G.Simple) (fx:Flick C.path.levels)(hk:1 ≤ M)
-- Jump exactly. adapting Snap. preserves Screen even for non generic tails, uses only pole exposures. Clock fixed ∼scale. affine y(r) already centered at PHYSICAL output.
private lemma exactJump {I ι:Type}[Fintype I][DecidableEq I] (S:Schedule){x:ι→ I→E4}(k:ι→ℕ): ∃ a: ℝ, 0 ≤ a∧ ∃ g:ι→ I→ Cover, (∀ i, Screen (S.gridPoint (k i) ∘ g i)) ∧ ∀ i, ‖(S.gridPoint (k i) ∘ g i)-x i‖ ≤ S.a (k i)*a:=by
    let K:ℤ:= Cloud.count I ∅; let g i:= Cloud.grid ∅ (S.a (k i)) (x i) (fun _ _=>0); let f(i):= S.gridPoint (k i) ∘ g i; have hk:0 < (K:ℝ):= Int.cast_pos.mpr (Cloud.count_pos _)
    refine ⟨2*K,by positivity,g,fun i=>Cloud.screened ∅ _ (S.a_pos _) _ _,fun i=>?_⟩; let z:= S.a (k i); have hp:0<z:= S.a_pos _; have hx(b:I)(a:Axis): ‖((f i-x i) b) a‖ ≤ z*K:= Cloud.close_zero ∅ z hp (x i) b a;
    rw [mul_left_comm]; apply (pi_norm_le_iff_of_nonneg (mul_nonneg zero_le_two (mul_pos hp hk).le)).2; intro b
    let d:= (f i-x i) b; have he: ‖d‖^2 ≤ 4*(z*K)^2:=by
       rw [EuclideanSpace.real_norm_sq_eq]; apply le_trans (Finset.sum_le_sum (g:=fun i:Axis=> (z*K)^2) (fun i hi=>?_ )); simp
       rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hx b _ ) _
    change ‖d‖≤_; nlinarith only [he,mul_pos hp hk]
include hz fx hk
set_option quotPrecheck false
local notation "T"=>OPE.run
lemma hopping (x v:ℝ→ Fin m→ E4)(hv:∀ᶠ i in home, ‖v i‖ ≤ 1/2) : ∃ (y:ℝ → Fin m→ E4) (p:ℝ→ Fin m→ Cover), (∀ i,Screen (C.S.gridPoint (wheel C i) ∘ p i)) ∧ (∀ᶠ i in home, ‖y i-v i‖ ≤ (2*freeZone (2*T i^2) M)⁻¹ ∧ ‖y i‖ ≤ 1 ∧ centered x id i (y i)= C.S.gridPoint (wheel C i) ∘ p i):=by
    let X:=fun i=> centered x id i (v i); obtain ⟨a,ha,g,hg,h⟩:= exactJump (x:=X) C.S (wheel C)
    let p i:= C.S.gridPoint (wheel C i) ∘ g i ; let H i:= T i/i; let y (i): Fin m→ E4:=v i+H i • (p i-X i); let w:=Real.exp 4; let Z:=32*M*w*w
    have hw:0<w:=Real.exp_pos _; have hK:0<M:=zero_lt_one.trans_le hk; have hz':1 ≤ Z:=by unfold Z; nlinarith only [hk, (show 1 ≤ w from Real.one_le_exp (by norm_num)), one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hk (show 1 ≤ w from Real.one_le_exp (by norm_num))) (show 1 ≤ w from Real.one_le_exp (by norm_num))]
    have ht:=ageLarge; let a':= G.slopeConstant/2; have ha' : 0<a':=half_pos (Gauge.slopeConstant_pos hz)
    refine ⟨y,g,hg,?_⟩; filter_upwards [ht.eventually_ge_atTop 2,(tollRatio (opt C fx hz)).eventually (le_mem_nhds (half_lt_self (Gauge.slopeConstant_pos hz))), ht.eventually_ge_atTop ((a*Z)/a'^7),positiveLength,hv] with i ht hv' hx hr hv
    let t:=T i; let b:=C.path.levels.clock.hatBeta (wheel C i); have hb:1≤ b:= (C.path.levels.fits.delayed _).le; have ht':1 ≤ t:=one_le_two.trans ht; have he:0<t:=zero_lt_one.trans_le ht'
    have hZ : 2*freeZone (2* T i^2) M= t^4*Z:=by unfold t Z freeZone w; ring
    have hh: ‖y i-v i‖ ≤ (t^4*Z)⁻¹:=by
       unfold y; rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (div_pos he hr|>.le)]; apply (mul_le_mul_of_nonneg_left ((h i).trans (mul_le_mul_of_nonneg_right ((le_div_iff₀ (pow_pos (zero_lt_one.trans_le hb) 7)).mpr (spoke C hr)) ha)) (div_pos he hr|>.le)).trans
       have hx': a*Z ≤ t*a'^7:= (div_le_iff₀ (pow_pos ha' _)).mp hx
       have hu: a*Z*t^5 ≤ b^7:=calc
          _ ≤ t*a'^7*t^5 := mul_le_mul_of_nonneg_right hx' (by positivity)
          _ = a'^7*t^6:=by ring
          _ ≤ a'^7*t^7:= by gcongr <;> linarith
          _ ≤ b^7:= by rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) ((le_div_iff₀ he).mp hv') _
       change t/i*(i/b^7*a)≤_; field_simp; linarith only [hu]
    refine ⟨hZ.symm ▸ hh,?_,?_⟩
    · have hμ: (t^4*Z)⁻¹ ≤ 1/2 := by rw [← one_div]; apply div_le_div_of_nonneg_left zero_le_one two_pos; exact ( (show 2 ≤ t^4 from le_trans ht ((pow_one t).symm.trans_le (pow_le_pow_right₀ ht' (by norm_num)))) ).trans (le_mul_of_one_le_right (by positivity) hz')
      linarith only [hh,hμ,hv,norm_sub_norm_le (y i) (v i)]
    unfold centered y; rw [smul_add, smul_smul, show id i / T (id i) * H i=1 from by change i/t*(t/i)=_; field_simp, one_smul, ← add_assoc]; change X i+(p i-X i)=_; abel
end YM.OPE.Polar.Joint17
