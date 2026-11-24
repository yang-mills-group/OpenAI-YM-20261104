import YM.UVExt.TraceShape
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.EnergyRay.Traces
open RG Wilson Function Set Filter Topology Metric MeasureTheory
open scoped BigOperators Topology ComplexConjugate Classical

variable {E ι : Type*} [MeasurableSpace E]

lemma deriv_m (f:E→ℂ→ℂ) (hm : ∀ z:ℂ,Measurable (fun x=>f x z)) (z:ℂ) (hf:∀ x,DifferentiableAt ℂ (f x) z) : Measurable (fun x=>deriv (f x) z) := by
 obtain ⟨u,h₁,h₂,H⟩:=exists_seq_strictMono_tendsto (0:ℝ)
 let v (n:ℕ):ℂ := (u n:ℝ)
 have hv : Tendsto v atTop (𝓝[≠] (0:ℂ)) := tendsto_nhdsWithin_iff.mpr ⟨Complex.continuous_ofReal.continuousAt.tendsto.comp H,Eventually.of_forall fun n=> mem_compl_singleton_iff.mpr (Complex.ofReal_ne_zero.mpr (h₂ n).ne)⟩
 let a n i := (v n)⁻¹ • ((f i (z+v n)) -f i z)
 apply measurable_of_tendsto_metrizable (f:=a) (fun n=> ((hm _).sub (hm z)).const_smul (v n)⁻¹)
 rw [tendsto_pi_nhds]; intro i; exact (HasDerivAt.tendsto_slope_zero (hf i).hasDerivAt).comp hv

lemma local_diff_integral {μ : Measure E} (f : E→ℂ→ℂ) (hm : ∀ z:ℂ,Measurable (fun x=>f x z)) {z:ℂ} {r:ℝ} (hr:0<r) (g:E→ℝ) (hf : ∀ x,DifferentiableOn ℂ (f x) (ball z r))
    (hg : Integrable g μ) (h : ∀ t∈ball z r,∀ x, ‖f x t‖ ≤ g x) : DifferentiableAt ℂ (fun y=> ∫ x,f x y ∂μ) z := by
 let f' (s:ℂ) (x:E):=deriv (f x) s
 let M:=4/r
 have hA (t) (he:t∈ball z r) (u:E) : HasDerivAt (f u) (f' t u) t := ((hf u t he).differentiableAt (isOpen_ball.mem_nhds he)).hasDerivAt
 have hb t (ht : t∈ball z (r/2)) : ball t (r/2) ⊆ ball z r := by
   intro s he; apply mem_ball.mpr; linarith [dist_triangle s t z,mem_ball.mp he,mem_ball.mp ht]
 have hc t (ht : t∈ball z (r/2)) (u:E) : ‖f' t u‖ ≤ M*g u := by
   have hS := hb t ht
   have he : Set.MapsTo (f u) (ball t (r/2)) (closedBall (f u t) (2*g u)) := by
      intro v hv; change dist _ _ ≤ _; rw [dist_eq_norm]; linarith [norm_sub_le (f u v) (f u t),h v (hS hv) u,h t (hS (mem_ball_self (half_pos hr))) u]
   have hD:= Complex.norm_deriv_le_div_of_mapsTo_ball ((hf u).mono hS) he (half_pos hr)
   dsimp [f',M]; exact hD.trans_eq (by ring)
 let hB := Metric.ball_mem_nhds (x:=z) (show 0<r/2 from half_pos hr)
 have hz : z∈ball z r := mem_ball_self hr
 have hm':Measurable (f' z) := deriv_m f hm _ (fun _=> (hA z hz _).differentiableAt)
 have hI := hg.mono (hm z).aestronglyMeasurable (Eventually.of_forall fun x=>(h z hz x).trans (le_abs_self _))
 exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=fun z x=>f x z) (F':=f') (bound:=fun x=>M*g x) hB (Eventually.of_forall fun s=>(hm s).aestronglyMeasurable) hI hm'.aestronglyMeasurable (Eventually.of_forall fun u t ht=> hc t ht u) (hg.const_mul M) (Eventually.of_forall fun u t ht=>hA _ (ball_subset_ball (by linarith) ht) u)).2.differentiableAt

lemma integrating (μ:Measure E) (f:E→ℂ→ℂ) (hm : ∀ z:ℂ,Measurable (fun x=>f x z)) (S: Finset ι)
    (k:ℕ) (hk:∀ x,∃ g:ι→Primitive, (∀ z:ℂ,0<z.re → f x z=bundled S g z) ∧ wage S g ≤ k)
    (I:Set ℝ) (hI:IsOpen I) (hi:I ⊆ Ioi 0) (hf : ∀ r∈I, Integrable (fun x=>f x (r:ℂ)) μ) : AnalyticOnNhd ℂ (fun y:ℂ=> ∫ x, f x y ∂μ) ((Complex.re)⁻¹' I) := by
 apply DifferentiableOn.analyticOnNhd _ (IsOpen.preimage Complex.continuous_re hI)
 intro z hz; change z.re ∈ I at hz
 obtain ⟨s,hs,hA⟩ := Metric.isOpen_iff.mp hI _ hz
 let r:=min (s/2) 1; have hr:0<r:=lt_min (half_pos hs) one_pos
 have hs' : r < s := lt_of_le_of_lt (min_le_left ..) (half_lt_self hs)
 let l:= z.re-r; let u:= z.re+r; have hl':l∈I := hA (by simpa only [l, mem_ball, Real.dist_eq, sub_sub_cancel_left,abs_neg,abs_of_pos hr]); have hu':u∈I:= hA (by simpa [u, mem_ball,Real.dist_eq,abs_of_pos hr])
 have hl:0<l:=hi hl'; have hu:0<u:=hi hu'
 let v x:=(((‖z‖+1)/l)^k * (u/l)^k) * (‖f x (l:ℂ)‖+‖f x (u:ℂ)‖)
 have hv (t:ℂ) (ht:t∈ball z r) : 0<t.re ∧ l≤t.re ∧ t.re≤u ∧ ‖t‖≤‖z‖+1 := by
   rw [mem_ball,dist_eq_norm] at ht
   have hb:|t.re-z.re| < r:= by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (t-z) |>.trans_lt ht
   exact ⟨by linarith [(abs_lt.mp hb).1],by linarith [(abs_lt.mp hb).1],by linarith [(abs_lt.mp hb).2],by linarith [norm_sub_norm_le t z,min_le_right (s/2) 1]⟩
 let A : Set ℂ:={y|0<y.re}; have he: ball z r⊆A:=fun t ht=>(hv t ht).1
 apply DifferentiableAt.differentiableWithinAt
 refine local_diff_integral f hm hr v (fun x=>?_) (((hf l hl').norm.add (hf u hu').norm).const_mul _) (fun t ht x=>?_)
 · obtain ⟨g,h,hG⟩:=hk x
   have hc : DifferentiableOn ℂ (bundled S g) A := by
     have h := DifferentiableOn.finsetProd (u:=S) (fun i _=> (g i).differentiable_run)
     rwa [show (∏ i∈S,(g i).run) = bundled S g from funext (fun z=>Finset.prod_apply z _ _)] at h
   exact (hc.mono he).congr fun y hy=>h y (he hy)
 obtain ⟨g,h,hG⟩:=hk x; have hS:= hv t ht
 unfold v; rw [h t hS.1, h _ hl, h _ hu]
 apply (strip_bound S g hl t hS.2.1 hS.2.2.1).trans (mul_le_mul_of_nonneg_right _ (add_nonneg (norm_nonneg _) (norm_nonneg _)))
 rw [mul_comm (((‖z‖+1)/l)^k) _]
 apply mul_le_mul

 
 · gcongr
   exact (one_le_div hl).mpr (hS.2.1.trans hS.2.2.1)
 · apply (pow_le_pow_right₀ ((one_le_div hS.1).mpr (Complex.re_le_norm _)) ?_).trans (pow_le_pow_left₀ (by positivity [hS.1]) ?_ k)
   · exact hG
   · exact div_le_div₀ (by positivity) hS.2.2.2 hl hS.2.1
 · positivity [hS.1]
 · positivity
end YM.UVExt.EnergyRay.Traces
