import YM.MSbar.Trust.Spilling
import YM.Gauge.Chart
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable (G:Gauge)
open Metric Next.Fluctuations
def maple (p:G.Color × G.Color):= G.plog (G.mat (G.lieExp p.1* G.lieExp p.2)) - p.1 - p.2
lemma mapleD : ContDiffAt ℝ ω (maple G) 0:=by
    let f(p:G.Color×G.Color):=G.mat (G.lieExp p.1*G.lieExp p.2); have hf:f 0=1:=by simp [f]
    have hh: ContDiff ℝ ω f:=by simp only [f,G.mat_mul]; apply (G.exp_jet.comp contDiff_fst).mul (G.exp_jet.comp contDiff_snd)
    exact (((hf.symm ▸ G.plog_diff: ContDiffAt ℝ ω G.plog (f 0)).comp (0:G.Color×G.Color) hh.contDiffAt).sub contDiffAt_fst).sub contDiffAt_snd
lemma spruce : ∃ C r:ℝ,0<C∧0<r∧∀ (R:ℝ),R≤r → ∀ A B:G.Color,‖A‖≤R→‖B‖≤R →‖maple G (A,B)‖≤C*R*‖A‖ :=by
   let f:=maple G; let E:=G.Color × G.Color
   have h : ContDiffAt ℝ ω f 0:= mapleD _
   have hx:=G.plog_left; have he:ContDiffAt ℝ 1 (fderiv ℝ f) 0:= h.fderiv_right (by simp)
   obtain ⟨C,S,hS,hz⟩:= he.exists_lipschitzOnWith
   have ht' : ∀ᶠ a:G.Color in 𝓝 0,f (0,a)=0 :=hx.mono fun i hi=> (by unfold f maple; simp only [G.mat_lieExp_zero, one_mul, hi]; abel)
   have ht : (fun a:G.Color=> f (a,0))=ᶠ[𝓝 0] (fun _=>0):=hx.mono fun i hi=> (by unfold f maple; simp only [G.mat_lieExp_zero,mul_one,hi]; abel)
   have hv:= (h.of_le (by simp : (1:WithTop ℕ∞) ≤ ω)).eventually (by simp) -- check
   obtain ⟨c,hc,hf⟩:= Metric.nhds_basis_closedBall.mem_iff.1 hS
   obtain ⟨r₀,hr,hg⟩:= Metric.nhds_basis_closedBall.eventually_iff.mp hv
   obtain ⟨d,hd,hD⟩:= Metric.nhds_basis_closedBall.eventually_iff.mp ht'
   let L: G.Color→L[ℝ] G.Color × G.Color:= ContinuousLinearMap.inl ℝ _ _; let g:=fderiv ℝ f
   have hG:(g 0).comp L=0:=by
      have hx : L 0=0:=map_zero _; have hh : HasFDerivAt f (g (L 0)) (L 0):= by rw [hx]; exact (h.differentiableAt (by simp)).hasFDerivAt
      have h₀ := hh.comp (0:G.Color) L.hasFDerivAt; rw [hx] at h₀
      exact (h₀.congr_of_eventuallyEq ht.symm).unique (hasFDerivAt_const ..)
   let s:=min c (min r₀ d); refine ⟨C+1,s,by positivity,lt_min hc (lt_min hr hd),fun R h b y hb hy=> ?_⟩
   have hV :0 ≤ R:=(norm_nonneg _).trans hb
   let w(x:G.Color):=(x,y); have hw u : HasFDerivAt w L u:=(hasFDerivAt_id _).prodMk (hasFDerivAt_const (x:=u) y)
   have hN(x:G.Color)(h:x∈ closedBall (0:G.Color) R): w x∈closedBall (0:E) R:= mem_closedBall.mpr (by rw [dist_zero_right]; exact max_le (by simpa using h) hy)
   have hd x (hp:x∈closedBall (0:G.Color) R) : HasFDerivAt (f∘w) ((g (w x)).comp L) x := (((hg (closedBall_subset_closedBall (h.trans (le_trans (min_le_right ..) (min_le_left ..))) (hN _ hp))).differentiableAt (by simp)).hasFDerivAt).comp _ (hw x)
   have hF(x:G.Color)(hp:x∈closedBall (0:G.Color) R): ‖fderiv ℝ (f∘w) x‖≤ C*R:=by
      rw [(hd x hp).fderiv]; have hi:= hz.dist_le_mul _ (hf (closedBall_subset_closedBall (h.trans (min_le_left ..)) (hN _ hp))) _ (hf (mem_closedBall_self hc.le))
      have hx:‖g (w x)-g 0‖ ≤ C*R :=by
        change dist (g _) (g 0) ≤ ↑C * dist (w x) 0 at hi; rw [dist_eq_norm] at hi; exact hi.trans (mul_le_mul_of_nonneg_left (mem_closedBall.mp (hN _ hp)) C.coe_nonneg)
      apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg C.coe_nonneg hV); intro j
      have he' := L.map_zero; have he : ((g (w x)).comp L) j=(g (w x)-g 0) (L j) :=by rw [← sub_zero (((g _).comp L) _), ← show (g 0) (L j)=0 from congr_arg (fun i:G.Color→L[ℝ] G.Color=>i j) hG]; rfl -- syntax
      rw [he]; exact ((g (w x)-g 0).le_opNorm _).trans ((mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans_eq (congr_arg _ (show ‖L j‖=‖j‖ from by change max ‖j‖ ‖(0:G.Color)‖= _; rw [norm_zero,max_eq_left (norm_nonneg _)])))
   have hl : f (w 0)=0:=hD (mem_closedBall.mpr (by rw [dist_zero_right]; exact hy.trans (h.trans (le_trans (min_le_right ..) (min_le_right ..)))))
   have hi := (convex_closedBall (0:G.Color) R).norm_image_sub_le_of_norm_fderiv_le (fun i hi=> (hd i hi).differentiableAt) hF (mem_closedBall_self hV) (mem_closedBall.mpr (show dist b 0 ≤ R from by rwa [dist_zero_right]))
   simp only [comp_apply,hl,sub_zero] at hi; apply hi.trans; gcongr; simp
end YM.MSbar.Heath
