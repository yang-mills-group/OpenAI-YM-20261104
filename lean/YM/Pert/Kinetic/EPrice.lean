import YM.Pert.Kinetic.Densities
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson RG AnalyticBridge.VerifiedReset
open scoped Topology BigOperators Classical ContDiff
variable {n : Side} {G : Gauge} {p : BudgetPoint} {δ w : ℝ} {A : Activities G n} (H : A.Valid p δ w) (hG : G.Simple)
include H hG
lemma additive_limit (v : Directions G n) (hD : ∀ o,p.dirBound o v) :
    Tendsto (fun t : ℝ=> A.additive p (line v t)/t^2) (𝓝[≠] 0) (𝓝 (∑' i, logHessian (A.E i) v v/2)) ∧
    Summable (fun i=>logHessian (A.E i) v v/2) := by
   obtain ⟨b,hb,hs,_⟩:= payment_sum H.boundE
   obtain ⟨y,hy,he⟩ := Metric.eventually_nhds_iff_ball.mp (rays_free (G:=G) p.threshold p.threshold_pos v)
   have hz {t : ℝ} (hx:|t| < y) (X : Support n) : Healthy p.threshold X (line v t) := by
      unfold Healthy; rw [he _ (Metric.mem_ball'.mpr (show dist (0:ℝ) t < y by rwa [Real.dist_eq,zero_sub,abs_neg]))]; exact disjoint_bot_right
   have hi (i:ℕ) : Tendsto (fun t=> A.regularOccurrence p i (line v t)/t^2) (𝓝[≠] 0) (𝓝 (logHessian (A.E i) v v/2)) := by
      refine (hessian_limit hG (H.regular.smooth i) (H.regular.at_flat i) v).congr' ?_
      filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℝ) hy)] with t ht
      unfold Activities.regularOccurrence; rw [masked_eq _ _ _ _ (hz (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht) _)]
   have hb' : Summable b := Summable.of_nonneg_of_le (fun i=>(hb i).1) (fun i=>(p.loMass _ _ (hb i).1)) hs
   have hU : ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ i, ‖A.regularOccurrence p i (line v t)/t^2‖ ≤ b i := by
       filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℝ) hy), self_mem_nhdsWithin (a:=0) (s:={0}ᶜ)] with t ht ht' i
       have ht'' : t ≠ (0:ℝ):= ht'
       unfold Activities.regularOccurrence
       rw [masked_eq _ _ _ _ (hz (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht) _),norm_div,Real.norm_of_nonneg (sq_nonneg _),div_le_iff₀ (sq_pos_of_ne_zero ht'')]
       exact line_bound v (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht) (fun x h => hz h _) (A.E i) (H.regular.smooth i) (hb i) (H.regular.at_flat i) hG (hD _)
   refine ⟨?_, Summable.of_norm_bounded hb' (fun i=>le_of_tendsto (hi i|>.norm) (hU.mono fun t ht=> ht i)) ⟩ -- g name?
   rw [show (fun t : ℝ=>A.additive p (line v t)/t^2)=(fun t=>∑' i,A.regularOccurrence p i (line v t)/t^2) by funext;rw [Activities.additive, ←tsum_div_const]]
   apply tendsto_tsum_of_dominated_convergence hb' hi hU

def Eread (v : Directions G n) := ∑' i, logHessian (A.E i) v v
include H hG
lemma frequencyE (c : G.Color) (hc : ‖c‖=1) (b : Bool) (i j : Axis) (hn : 4 ≤ n.val) :
    let v : Directions G n := wave c b i j
    |Eread (A:=A) v| ≤ (Full.mesh n)^3 * geomE p * (Fintype.card (Site n)*δ) := by
   intro v
   obtain ⟨z,k,h,hz⟩:= payment_sum H.boundE
   have hf(a):= one_fee c hc b (hG:=hG) (i:=i) (j:=j) (A.reg a).site (H.regular.smooth a) (A.reg a).anchor (k a) (H.regular.vanish a) hn
   have he := Real.exp_pos (0:ℝ)
   let m:ℝ:=(Full.mesh n)^3* geomE p
   have hm : 0≤ m := by unfold m geomE; have ht:=p.threshold_pos;have hQ:=p.exponent_pos;have hw:=Full.mesh_pos (n:=n);have hπ:=Real.pi_pos; positivity
   have hh(a):‖logHessian (A.E a) v v‖ ≤ m*p.mass (A.reg a).support (z a) := hf a
   change ‖∑' i,logHessian (A.E i) v v‖ ≤ _
   refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (by intros; positivity) hh (h.mul_left m))).trans ?_
   refine ((Summable.of_nonneg_of_le (by intros; positivity) hh (h.mul_left m)).tsum_le_tsum hh (h.mul_left m)).trans ?_
   rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hz hm
end YM.Pert.Kinetic
