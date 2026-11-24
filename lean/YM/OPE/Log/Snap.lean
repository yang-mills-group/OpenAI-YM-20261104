import YM.OPE.Log.Rail
/-! # Render nearest generic point -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open Filter Function Set Metric Lattice RG Polar
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{ι I:Type}[Fintype I][DecidableEq I] {l: Filter ι}{r:ι→ℝ}(hr:Tendsto r l (𝓝[>] 0))
    {K:ℝ}{k m j:ι→ℕ}
private lemma exactJump (S:Schedule){x:ι→ I→E4}(k:ι→ℕ): ∃ a: ℝ, 0 ≤ a∧ ∃ g:ι→ I→ Cover, (∀ i, Screen (S.gridPoint (k i) ∘ g i)) ∧ ∀ i, ‖(S.gridPoint (k i) ∘ g i)-x i‖ ≤ S.a (k i)*a:=by
    let K:ℤ:= Cloud.count I ∅; let g i:= Cloud.grid ∅ (S.a (k i)) (x i) (fun _ _=>0); let f(i):= S.gridPoint (k i) ∘ g i; have hk:0 < (K:ℝ):= Int.cast_pos.mpr (Cloud.count_pos _)
    refine ⟨2*K,by positivity,g,fun i=>Cloud.screened ∅ _ (S.a_pos _) _ _,fun i=>?_⟩; let z:= S.a (k i); have hp:0<z:= S.a_pos _; have hx(b:I)(a:Axis): ‖((f i-x i) b) a‖ ≤ z*K:= Cloud.close_zero ∅ z hp (x i) b a;
    rw [mul_left_comm]; apply (pi_norm_le_iff_of_nonneg (mul_nonneg zero_le_two (mul_pos hp hk).le)).2; intro b
    let d:= (f i-x i) b; have he: ‖d‖^2 ≤ 4*(z*K)^2:=by
       rw [EuclideanSpace.real_norm_sq_eq]; apply le_trans (Finset.sum_le_sum (g:=fun i:Axis=> (z*K)^2) (fun i hi=>?_ )); simp
       rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hx b _ ) _
    change ‖d‖≤_; nlinarith only [he,mul_pos hp hk]

include hr
local notation "W"=> (fun i=>run (r i))
lemma snap (hk:1 ≤ K)(hj:∀ᶠ i in l, C.S.a (j i) < r i/W i^32) (x v:ι→ I→ E4) (hv:∀ᶠ i in l, ‖v i‖≤1/2) : ∃ (y:ι→ I→E4)(p:ι→ I→ Cover), (∀ i, Screen (C.S.gridPoint (j i) ∘ p i)) ∧ ∀ᶠ i in l,‖y i-v i‖ ≤ (2*freeZone (W i^2) K)⁻¹ ∧ ‖y i‖ ≤ 1 ∧ centered x r i (y i)= C.S.gridPoint (j i) ∘ p i:=by
    let X:=fun i=> centered x r i (v i); obtain ⟨a,ha,g,hg,h⟩:= exactJump (x:=X) C.S j
    let p i:= C.S.gridPoint (j i) ∘ g i ; let H i:= W i/r i; let y (i):I→ E4:=v i+H i • (p i-X i); let w:=Real.exp 4; let Z:=8*K*w*w
    have hw:0<w:=Real.exp_pos _; have hK:0<K:=zero_lt_one.trans_le hk; have hz:1 ≤ Z:=by unfold Z; nlinarith only [hk, (show 1 ≤ w from Real.one_le_exp (by norm_num)), one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hk (show 1 ≤ w from Real.one_le_exp (by norm_num))) (show 1 ≤ w from Real.one_le_exp (by norm_num))]
    have ht:=run_towards hr; refine ⟨y,g,hg,?_⟩; filter_upwards [ht.eventually_ge_atTop 2,ht.eventually_ge_atTop (a*Z),hj,(loglife hr).pos,hv] with i ht hx hj hr hv
    let t:=run (r i); have ht':1 ≤ t:= one_le_two.trans ht; have he: 0<t:=zero_lt_one.trans_le ht'; have hY': H i*(r i /t)=1:=by unfold H; dsimp only; unfold t; field_simp -- simplify positivity?
    have hZ : 2*freeZone (W i^2) K= t^4*Z:=by unfold t Z freeZone w; ring
    have hh: ‖y i-v i‖ ≤ (t^4*Z)⁻¹:= by
       unfold y; rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (div_pos he hr|>.le)]; apply (mul_le_mul_of_nonneg_left ((h i).trans (mul_le_mul_of_nonneg_right hj.le ha)) (div_pos he hr|>.le)).trans
       have hu: t*(t^4*(a*Z)) ≤ t^32:= calc
          _ ≤ t*(t^4*t):= by gcongr
          _ ≤ _:= by rw [show t*(t^4*t)=t^6 by ring]; exact pow_le_pow_right₀ ht' (by norm_num)
       change t/r i*(r i/t^32*a) ≤ _; have hZ:0<Z:=zero_lt_one.trans_le hz; field_simp; exact hx.trans ((pow_one t).symm.trans_le (pow_le_pow_right₀ ht' (by norm_num)))
    refine ⟨hZ.symm ▸ hh,?_,?_⟩
    · have hu:(t^4*Z)⁻¹ ≤ 1/2 := by rw [← one_div]; apply div_le_div_of_nonneg_left zero_le_one two_pos; exact ( (show 2 ≤ t^4 from le_trans ht ((pow_one t).symm.trans_le (pow_le_pow_right₀ ht' (by norm_num)))) ).trans (le_mul_of_one_le_right (by positivity) hz)
      linarith only [hh,hu,hv,norm_sub_norm_le (y i) (v i)]
    unfold centered y; rw [smul_add, smul_smul,mul_comm (_/_) (H i),hY',one_smul, ← add_assoc]; change X i+(p i-X i)=_; abel
end YM.OPE.Log
