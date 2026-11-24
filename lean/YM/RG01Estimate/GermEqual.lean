import YM.RG01Estimate.Wrap
/-!
 # Exact pre-reset projected comparability at the SAME alpha, beta, with any τ.
 Need charge sharp for wrapping E* before applying Δ; afterwards unusable due to reserve.
 Positivity neighborhood may shrink with volume; blanket uses only post-value regular norms.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Censor
open Function Filter Set Lattice Wilson RG AnalyticBridge VerifiedReset Collection Averaging
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}{p:BudgetPoint}{X:Support n}{a K:Listing G n}{v W:Collection.Source G n}
    (g:G.Simple) {f:Pot G n} {u H d D' β τ τ' α:ℝ} {C:Clip}{S:PathData G}
    (H':Local a p v H u)(h':Local K p W D' d)

include H' g
namespace Along
lemma jurors (z : Directions G n) (hD:∀ o,p.dirBound o z):
   Tendsto (fun t:ℝ=>((a.read v).additive p (line z t)-(a.read v).additive p 1)/t^2) (𝓝[≠] 0) (𝓝 ((∑' i,logHessian (v.logRead i) z z)/2)) ∧
    Summable fun i=> logHessian (v.logRead i) z z :=by
    let a' := a.read v; let F i:Pot G n := v.logRead i-fun _ => v.logRead i 1
    obtain ⟨b,hb,he'⟩:=Activities.E_total H'.unweighted
    obtain ⟨x,hx,hT⟩:= Metric.eventually_nhds_iff_ball.mp (Pert.Kinetic.rays_free (G:=G) p.threshold p.threshold_pos z)
    have hz {t:ℝ} (h: |t| <x) (X:Support n) : Healthy p.threshold X (line z t):= by
       unfold Healthy; rw [hT _ (Metric.mem_ball'.mpr (show dist (0:ℝ) t < x by rwa [Real.dist_eq,zero_sub,abs_neg]))]; exact disjoint_bot_right
    have hR i: p.Regular (a.reg i).support (F i):= reg_sub (H'.smooth i) (reg_const _)
    have hg i: F i 1=0:=by simp only [F,Pi.sub_apply,sub_self];
    have he i: Tendsto (fun t:ℝ=> ((a.read v).regularOccurrence p i (line z t)-(v.logRead i 1))/t^2) (𝓝[≠] 0) (𝓝 (logHessian (v.logRead i) z z/2)) := by
       have hd (j) : logHessian (F j) z z=logHessian (v.logRead j) z z:= by
          unfold F; rw [hessian_sub (H'.smooth j) (reg_const _),hessian_zero,sub_zero]
       rw [← hd i]; refine (hessian_limit g (hR i) (hg i) z).congr' ?_
       filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℝ) hx)] with t ht
       rw [Activities.regularOccurrence, masked_eq _ _ _ _ (hz (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht) _)]; rfl
    have hw : ∀ᶠ t:ℝ in 𝓝[≠] 0,∀ i, ‖((a.read v).regularOccurrence p i (line z t)-v.logRead i 1)/t^2‖ ≤ b i+b i:= by
       filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℝ) hx),self_mem_nhdsWithin (a:=0) (s:={0}ᶜ)] with t ht hn i
       have hq : |t|<x:= by simpa [Real.dist_eq] using ht
       have hs:= sup_const (o:=(a.reg i).site) (p:=p) (X:=(a.reg i).support) (G:=G) (v.logRead i 1)
       have hχ : _ := (sup_sub (H'.smooth i) (reg_const (v.logRead i 1)) (he' i) hs) -- tweak
       have hP: p.supBounds _ _ (F i) (b i+b i):= sup_le hχ (add_le_add_right ((he' i).2 1 (flat_ok p _) [] (by simp) (by simp)) _)
       rw [Activities.regularOccurrence,masked_eq _ _ _ _ (hz hq _),norm_div,Real.norm_of_nonneg (sq_nonneg _), div_le_iff₀ (sq_pos_of_ne_zero (show t≠(0:ℝ) from hn))]
       exact Pert.Kinetic.line_bound z hq (fun x h=> hz h _) (F i) (hR i) hP (hg i) g (hD _)
    have ht: Summable (fun i=> logHessian (v.logRead i) z z /2):= Summable.of_norm_bounded (hb.add hb) (fun i=> le_of_tendsto (he i|>.norm) (hw.mono fun t h=>h i))
    refine ⟨?_,(ht.mul_right 2).congr (fun i=> by ring)⟩
    rw [← tsum_div_const]
    refine (tendsto_tsum_of_dominated_convergence (hb.add hb) he hw).congr ?_
    intro t; rw [tsum_div_const]; unfold Activities.additive
    congr 1
    have hV' := H'.unweighted; have hm (U:Config G n): Summable fun i => (a.read v).regularOccurrence p i U:=
       (YM.Next.Rank.Alarm.ante p _ hV' _ ) -- locate
    rw [ (hm (line z t)).tsum_sub ]
    · congr 2 with i; rw [Activities.regularOccurrence,masked_eq _ _ _ _ (flat_ok p _)]; rfl
    have h:= hm 1; exact h.congr (fun i=> by rw [Activities.regularOccurrence,masked_eq _ _ _ _ (flat_ok p _)]; rfl)
end Along
end YM.RG01Estimate.Censor
