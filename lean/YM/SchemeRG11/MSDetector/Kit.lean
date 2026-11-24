import YM.SchemeRG11.Flare.Rune
/-!
Freeze proper-time cutoff on contractions. Applies both before and
in pole-dressing. Does NOT discard identity mixing/vacuum free
contractions in building amplitudes.
-/
set_option autoImplicit false
set_option maxHeartbeats 330000
noncomputable section
namespace YM.SchemeRG11.MSDetector
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter TopologicalSpace Cluster Steam MSbar Pert Triangle Storm Flare Bubble
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
abbrev Bins := Fin 4

def weight : Bins→ℝ:= ![4,-6,4,-1]
def times (i : Bins) : ℝ:= ↑(i.val+1)
def peak (R : ℝ) (i : Bins) := times i*R
lemma peak_pos (i : Bins) : 0<times i:= Nat.cast_pos.mpr (Nat.succ_pos _)
lemma peak_ge (i : Bins){R : ℝ}(hr : 1≤R) : 1≤peak R i := one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr (Nat.le_add_left 1 _)) hr

def stamp (s R : ℝ):= (1-Real.exp (-s*R))^4
lemma weight_add : ∑ i:Bins,weight i=1:=by norm_num [Bins,weight, Fin.sum_univ_succ]

lemma realizes {s R : ℝ} (hs : 0<s) (hr : 1≤R) :
    (∑ i:Bins,weight i*∫ t in Ioc 0 (peak R i),Real.exp (-t*s)) = stamp s R / s := by
  have he i : (∫ t in Ioc 0 (peak R i),Real.exp (-t*s))=(1-Real.exp (-s*R)^((i:Bins).1+1))/s := by
    let F:=fun t:ℝ=> (1-Real.exp (-t*s))/s
    have hd (t:ℝ): HasDerivAt F (Real.exp (-t*s)) t := by
       convert! ((((((hasDerivAt_id' t).neg).mul_const s).exp).const_sub 1).div_const s) using 1; dsimp; field_simp
    have hp:= intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=F) (a:=0) (b:=peak R i) (fun t _=>hd t) ((continuous_iff_continuousAt.mpr fun _=> Real.continuous_exp.continuousAt.comp (show ContinuousAt _ _ by fun_prop)).intervalIntegrable _ _)
    rw [intervalIntegral.integral_of_le (zero_le_one.trans (peak_ge i hr))] at hp; rw [hp]
    unfold peak times F; simp only [neg_zero,zero_mul,Real.exp_zero,sub_self,zero_div,sub_zero,← Real.exp_nat_mul]; push_cast; ring_nf
  simp_rw [he,stamp]; simp [weight,Bins,Fin.sum_univ_succ]; ring

variable {ι E : Type} {v : Filter ι} [NormedAddCommGroup E] [NormedSpace ℝ E]
def weigh (f : Bins→E): E := ∑ i,weight i • f i
lemma entire (e : E): weigh (fun _=> e)=e:=by unfold weigh; rw [← Finset.sum_smul, weight_add, one_smul]
lemma lifted {f : ι→Bins→E} {e : E} (h : ∀ i,Tendsto (fun y=> f y i) v (𝓝 e)) : Tendsto (fun y=> weigh (f y)) v (𝓝 e):= by
  simpa only [entire] using (show Tendsto (fun y=>weigh (f y)) v (𝓝 (weigh fun _:Bins=>e)) from tendsto_finsetSum Finset.univ fun i _=>tendsto_const_nhds.smul (h i))
abbrev ends (i : Bins) {p : ι→ℝ} (h : Tendsto p v atTop) : Tendsto (fun y=>peak (p y) i) v atTop:= (tendsto_const_mul_atTop_of_pos (peak_pos i)).mpr h

variable {μ : ℝ} (hμ: 0<μ) {n : ℕ}

/-- open Fourier line, external momentum letters. -/
def pulse (μ R : ℝ) (U : List (Fin n)) (z : ℂ) (x : Hot.Space n) := weigh (fun i=> gear (plume μ U) (peak R i) x z 0)
include hμ
theorem pulses (R : ℝ) (U : List (Fin n)){x : Hot.Space n}(hx:x≠0) : Differentiable ℂ (fun z=>pulse μ R U z x) := by
  unfold pulse weigh; refine Differentiable.fun_sum (fun i _=> ?_); apply Differentiable.const_smul
  exact Bubble.pulse (hemp hμ _) hx 0 le_rfl

def star (μ R : ℝ) (U : Cluster.Sweep n) (z : ℂ) (x : Nodes n) :=
   weigh fun i=> weigh fun j=> weigh fun k=> badge μ (peak R i) (peak R j) (peak R k) U z x
lemma stars (R : ℝ) (U : Cluster.Sweep n) {x : Nodes n} (hx:x∈clearance n) : Differentiable ℂ (fun z=> star μ R U z x) := by
  unfold star weigh; apply Differentiable.fun_sum; intro i _; apply Differentiable.const_smul; apply Differentiable.fun_sum; intro j _; apply Differentiable.const_smul; exact Differentiable.fun_sum (fun k _=> (suffix hμ U hx).const_smul _)

omit hμ in
lemma pulse4 (R : ℝ) (U : Sl) (x:E4): pulse μ R U 0 x=weigh fun i=>(↑(∫ t in Ioc 0 (peak R i), Steam.tint U t x):ℂ) := by
  simp only [pulse,gear,add_zero,← melt,integral_complex_ofReal]
end YM.SchemeRG11.MSDetector
