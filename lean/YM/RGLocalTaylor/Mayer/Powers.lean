import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Suites
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Order

/-!
# Local logarithmic Taylor prescription and power estimates

In the *Mayer* comparison (Taylor in the interaction exponents), use true
finite-order Taylor, not just tail by number of heads. The input is `y` (small
profiled exponent or inherited interaction), supplied in E6 as `e = exp(y)-1`.
Render the Taylor coefficients of `exp(ζ*y)-1` at ζ=0, through the requested
order and with no constant term. Use a globally smooth extension of the recovery
`log(1+e)` to interface faithfully with the support and mask interpretation in
E6. The extension is inactive for all eligible fields after dressing the vertices.

This Taylor parameter does *not* multiply the physical link field, BP kernel
penalty or beta/schedule/hard masks. When obtaining coupling powers one must
show that each y really carries coupling power (after all the deterministic and
Gaussian and derivative transformations), and, because normalized sizes per y can
be larger than g, impose enough **internal order** given the number of coupling
powers requested. Thus, not yet a bare-coupling Taylor formula with coefficients
independent of the history. This expansion inside the integral is intended in
particular for use before that comparison or with full effective kernels as inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Mayer
open Filter Function Finset Metric
open scoped Topology ContDiff BigOperators Classical
open ConnectedActivityE6.Blaze

private def collar : ContDiffBump (0:ℝ) := ⟨1/4,1/2,by norm_num,by norm_num⟩

def recoverLog (x:ℝ) := Real.log (1+x*collar x)

private lemma recover_pos (x : ℝ) : 0 < 1+x*collar x := by
  by_cases hp : x ∈ Metric.ball (0:ℝ) (1/2:ℝ)
  swap; · have he:x ∉ Function.support (collar.toFun):= by rw [show collar.toFun=⇑collar from rfl, collar.support_eq]; exact hp
          have hh : collar x=0:= Function.notMem_support.mp he; rw [hh]; simp
  have hr:= collar.le_one (x:=x); have hh:= collar.nonneg (x:=x)
  have ht:= (abs_lt.mp (mem_ball_zero_iff.mp hp : |x| < _)).1
  rcases lt_or_ge x 0 with h|h
  · nlinarith
  positivity

lemma log_smooth (j : ℕ) : ContDiff ℝ (↑j) recoverLog :=
  ContDiff.log (contDiff_const.add (contDiff_id.mul collar.contDiff)) fun x=> (recover_pos x).ne'

lemma honest_log (x : ℝ) (he : |x|≤1/4) : recoverLog x=Real.log (1+x) := by
  unfold recoverLog; rw [collar.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr he),mul_one]

lemma local_log : recoverLog=ᶠ[𝓝 (0:ℝ)] fun x=>Real.log (1+x) := by
  filter_upwards [closedBall_mem_nhds (x:=(0:ℝ)) (by norm_num : (0:ℝ)<1/4)] with x hx using
    honest_log x (mem_closedBall_zero_iff.mp hx)
lemma recovers (x : ℝ) (he : |Real.exp x-1|≤1/4) : recoverLog (Real.exp x-1)=x:= by rw [honest_log _ he,add_sub_cancel,Real.log_exp]

/-- positive-order Taylor coefficient in the interaction. -/
def atOrder (i : ℕ) (x : ℝ) := (recoverLog x)^(i+1)/(i+1).factorial

/-- Finite splitting with no constant. Keep `k=1,…,M`; index `(k-1)`.
Last slot is ONLY the tail; in particular can use also with `M=0`. -/
def indexValue {M : ℕ} (i : Fin (M+1)) (x : ℝ) := if i.val=M then
    x - ∑ j∈range M, atOrder j x else atOrder i.val x

lemma index_cast {M : ℕ} (i : Fin M) : indexValue i.castSucc=atOrder i.val :=
  funext fun _ => if_neg (ne_of_lt i.isLt)
lemma index_last (M : ℕ) (x:ℝ) : indexValue (Fin.last M) x=x- ∑ j∈range M, atOrder j x:= if_pos (Fin.val_last ..)

/-- Kernel equality (including the supplied nonlinear error). -/
lemma index_identity (M : ℕ) (x : ℝ) : ∑ i:Fin (M+1),indexValue i x=x:= by
  rw [Fin.sum_univ_castSucc, index_last]; simp_rw [index_cast]; rw [Fin.sum_univ_eq_sum_range (fun i=>atOrder i x)]; ring

lemma index_interior {M : ℕ} (i: Fin M) (x : ℝ) (he : |Real.exp x-1|≤1/4) :
    indexValue i.castSucc (Real.exp x-1)= x ^ (i.val+1) / (i.val+1).factorial := by rw [index_cast,atOrder,recovers x he]

lemma smooth (j : ℕ) {M : ℕ} (i : Fin (M+1)) : ContDiff ℝ (↑j) (indexValue i) := by
  unfold indexValue; split_ifs
  next _ => exact contDiff_id.sub (ContDiff.sum fun i _=> ((log_smooth j).pow _).div_const _)
  exact ((log_smooth j).pow _).div_const _

private lemma vanishes_log : ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧ recoverLog=ᶠ[𝓝 (0:ℝ)] fun x=> x*g x := by
  let f(x:ℝ):= Real.log (1+x)
  have h : AnalyticAt ℝ f 0:= AnalyticAt.log (analyticAt_const.add analyticAt_id) (by norm_num)
  obtain ⟨g,hG,H⟩:= h.exists_eventuallyEq_sum_add_pow_mul 1
  refine ⟨g,hG, local_log.trans (Eventually.mono H (fun z hz=>?_))⟩
  simpa [f] using hz

-- Estimate powers including the last slot via the theorem with ANALYTIC tail
-- only near zero; the full function must still be smooth.
private lemma term_factors (i : ℕ) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧ atOrder i =ᶠ[𝓝 0] fun x:ℝ=> x^(i+1)*g x := by
  obtain ⟨g,hg,h⟩:= vanishes_log
  refine ⟨fun x=> (g x)^(i+1)/(i+1).factorial,?_,?_⟩
  · simp_rw [div_eq_mul_inv]; exact (hg.pow _).mul analyticAt_const
  filter_upwards [h] with x hx; unfold atOrder; rw [hx,mul_pow,mul_div_assoc]

private lemma factors (j M : ℕ) (i : Fin (M+1)) :
    ∃ g : ℝ → ℝ, ContDiffAt ℝ (↑j) g 0 ∧ indexValue i =ᶠ[𝓝 0] fun x=> x^(i.val+1)*g x := by
  by_cases he:i.val=M
  swap; · obtain ⟨g,hg,h⟩:= term_factors i.val; exact ⟨g,hg.contDiffAt,h.mono fun x ht => (if_neg he).trans ht⟩
  obtain ⟨g,hg,hG⟩:= (analyticAt_rexp).exists_eventuallyEq_sum_add_pow_mul (M+1)
  have hL:recoverLog 0=0:=by rw [honest_log _ (by norm_num)]; norm_num
  obtain ⟨k,hk,H⟩:=vanishes_log
  refine ⟨fun x=> k x^(M+1)*g (recoverLog x), (hk.contDiffAt.pow _).mul ((hL.symm ▸ hg.contDiffAt).comp (f:=recoverLog) _ (log_smooth j|>.contDiffAt)),?_⟩
  filter_upwards [H,local_log,( (log_smooth j).continuous.continuousAt : ContinuousAt recoverLog 0) (hL.symm ▸ hG),closedBall_mem_nhds (x:=(0:ℝ)) (by norm_num : (0:ℝ)<1/4)] with x h hp he' hT
  have hg' i:iteratedDeriv i Real.exp 0=1:=by rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp,Real.exp_zero]
  have hX:0<1+x:= by have hh:= (abs_le.mp (mem_closedBall_zero_iff.mp hT : |x|≤_)).1; linarith
  simp only [Set.mem_preimage, Set.mem_setOf_eq,hL,hg'] at he'
  rw [Finset.sum_range_succ',hp,Real.exp_log hX] at he'
  rw [indexValue,if_pos he]; simp only [smul_eq_mul,mul_one,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one] at he'
  simp_rw [atOrder]; simp_rw [← hp] at he'
  rw [show x^(i.val+1)*(k x^(M+1)*g (recoverLog x))=recoverLog x^(M+1)*g (recoverLog x) by rw [he,h,mul_pow]; ring]
  linarith

-- keep its Taylor interpretation visible on the whole price range
lemma true_exponent_taylor (i : ℕ) (x : ℝ) (he : |Real.exp x-1|≤1/4) :
    atOrder i (Real.exp x-1)=
      iteratedDeriv (i+1) (fun s:ℝ=> Real.exp (x*s) - 1) 0/(i+1).factorial := by
  rw [atOrder,recovers x he,iteratedDeriv_fun_sub ?_ (contDiffAt_const),
    iteratedDeriv_exp_const_mul]; simp [iteratedDeriv_const]
  fun_prop

/-- Estimates for all dimensions simultaneously, including through `order`
at an actual full-speed brush. -/
structure Approved (K C : ℝ) (order M : ℕ) : Prop where
  pos : 0 < K
  small : K ≤ 1/4
  nonneg : 1 ≤ C
  estimated {E:Type} [_hE : NormedAddCommGroup E] [_hER : NormedSpace ℝ E]
    (f : E → ℝ) (w u : ℝ) (x : E) : Brush order u w f x → u ≤ K → ∀ i : Fin (M+1),
      Brush order (C*u^(i.val+1)) ((M+4:ℝ)*w) (fun z => indexValue i (f z)) x

lemma brush_power {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ}
    {u d:ℝ} {f : E → ℝ} {x:E} (p:Brush j u d f x) (n:ℕ) :
    Brush j (u^n) ((n:ℝ)*d) (fun y=> f y^n) x:=by
  induction n with
  | zero => simpa only [pow_zero,Nat.cast_zero,zero_mul,norm_one] using! (Brush.certified (x:=x) (k:=j) (le_refl 0) (1:ℝ))
  | succ n ih=> simpa only [pow_succ,Nat.cast_add_one,add_mul, one_mul] using! ih.paints p

lemma approved (j M : ℕ) : ∃ K C:ℝ, Approved K C j M := by
  choose g hg h using (fun i: Fin (M+1)=> factors j M i)
  choose c hc hF using (fun t=>Brush.neighborhood _ (hg t))
  obtain ⟨K,hK,hG⟩:= Metric.mem_nhds_iff.mp ((eventually_all.mpr (fun i=> ((eventually_eventually_nhds.mpr (h i)).and (hF i)))))
  let C : ℝ := 1+ ∑ i,j.factorial*c i
  have hz i : 0 ≤ j.factorial*c i:= mul_nonneg (Nat.cast_nonneg _) (hc i).le
  have hC:1≤C:= le_add_of_nonneg_right (sum_nonneg fun i _ => hz i)
  refine ⟨min (1/4) (K/2),C,lt_min (by norm_num) (half_pos hK),min_le_left ..,hC,?_⟩
  intro E _ _ f w u x hf hs i
  have hm : f x∈Metric.ball 0 K := mem_ball_zero_iff.mpr ((hf.bound.trans (hs.trans (min_le_right ..))).trans_lt (half_lt_self hK))
  obtain ⟨h₁,h₂⟩:= hG hm i
  have hu : u ≤ 1:= hs.trans ((min_le_left ..).trans (by norm_num))
  refine ((((brush_power hf (i.val+1)).paints (hf.pine h₂)).shimmy (hf.smooth.continuousAt.tendsto.eventually h₁)).climb ?_ ?_)
  · rw [mul_comm]; exact mul_le_mul_of_nonneg_right ((single_le_sum (s:=univ) (fun i _=> hz i) (mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)) (pow_nonneg hf.nonneg _)
  have hv': ((i.val+1:ℕ):ℝ)+(1+u)≤ M+4:=by
    push_cast; have he:(i.val:ℝ)< (M:ℝ)+1:=by exact_mod_cast i.isLt
    linarith
  rw [← add_mul]; exact mul_le_mul_of_nonneg_right hv' hf.pos

end YM.RGLocalTaylor.Mayer
