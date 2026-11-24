import YM.MSbar.Symbol.HolJet
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.TaylorSeries

/-! Trick for continuing Mellin operations on temperate symbols with a holomorphic parameter.
Require weight continuous also to boundary; choose exponent by stages. Do not assume
its parameter path is a continuation as functional over any unbounded symbols. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Symbol
open Function Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff BigOperators Classical
namespace AH
variable {E X Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {U : Set ℂ} {c z : ℂ} {r : ℝ}
local notation "Θ" => (Icc 0 (2*Real.pi))
lemma localized {g : ℂ×X→ℂ} {K : Set X} (hu : IsOpen U) (hf : ∀ y:ℂ×X,y.1∈ U → ContDiffAt ℝ ∞ g y)
    (hg : ∀ (z:ℂ) (x:X), z∈U → DifferentiableAt ℂ (fun w=> g (w,x)) z)
    (hc : IsCompact K) (hp : ∀ z∈U,∀ x∉K,g (z,x)=0) : AH U g := by
    refine ⟨fun z hz=> ?_,hg⟩
    obtain ⟨r,hr,H⟩:= Metric.mem_nhds_iff.mp (hu.mem_nhds hz)
    let b : ContDiffBump z := ⟨r/3,r/2,by positivity,by linarith⟩
    let f (q:ℂ×X):= b q.1 • g q
    have hl : b.rOut < r:= half_lt_self hr
    have hZ(q:ℂ×X) (hQ : q∉ closedBall z b.rOut ×ˢ K): f q=0:=by
       by_cases ht : q.1∈ closedBall z b.rOut
       · unfold f; rw [hp q.1 (H ((closedBall_subset_ball hl) ht)) _ (fun h=> hQ ⟨ht,h⟩),smul_zero]
       unfold f; rw [b.zero_of_le_dist (le_of_lt (lt_of_not_ge ht)),zero_smul]
    have hF : HasCompactSupport f:= ((isCompact_closedBall _ _).prod hc).of_isClosed_subset isClosed_closure (closure_minimal (fun y hy => by contrapose! hy; simpa using hZ y hy) (isClosed_closedBall.prod hc.isClosed))
    have hs : ContDiff ℝ ∞ f:=by
        apply contDiff_iff_contDiffAt.mpr; intro q
        by_cases ht:q.1∈ ball z r
        · exact (b.contDiff.contDiffAt.comp q contDiffAt_fst).smul (hf q (H ht))
        have hm :q∉ closedBall z b.rOut ×ˢ K:= fun h=> ht ((closedBall_subset_ball hl) h.1)
        exact (contDiffAt_const (c:=0)).congr_of_eventuallyEq ((show ∀ᶠ y in 𝓝 q,y∉ closedBall z b.rOut ×ˢ K from (isClosed_closedBall.prod hc.isClosed).isOpen_compl.mem_nhds hm).mono fun y hy=> hZ y hy)
    refine ⟨f,hF.hasTemperateGrowth hs,b.eventuallyEq_one.mono fun t ht=> ?_⟩
    funext i; simp [f,ht]

lemma get_kernel (hr : 0<r) : ∃ f : ℂ×ℝ→ℂ, AH (ball c r) f ∧ ∀ z t,t∈ Θ → f (z,t)=(circleMap c r t-z)⁻¹:=by
    let b : ContDiffBump (0:ℝ):= ⟨_,2*Real.pi+1,Real.two_pi_pos,lt_add_one _⟩
    let p (t:ℝ):= (↑(b t):ℂ);let f (z:ℂ×ℝ):=p z.2*(circleMap c r z.2-z.1)⁻¹
    have hz z (t:ℝ) (he:z∈ ball c r): circleMap c r t-z ≠ 0:=by
        intro h; rw [← sub_eq_zero.mp h] at he; have hx : circleMap c r t ∈ sphere c r:= circleMap_mem_sphere c hr.le t; change dist _ _=r at hx; exact hx.not_lt he
    refine ⟨f,localized isOpen_ball (fun q h=>?_) (fun z x h=>?_) (isCompact_closedBall (0:ℝ) b.rOut) (fun z _ x h=>?_),fun z t ht=>?_⟩
    · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (b.contDiff.contDiffAt.comp q contDiffAt_snd)).mul ((((contDiff_circleMap c r).contDiffAt.comp q contDiffAt_snd).sub contDiffAt_fst).inv (hz q.1 q.2 h))
    · exact ((differentiableAt_const _).sub differentiableAt_id).inv (hz _ _ h) |>.const_mul (p x)
    · unfold f p; dsimp only; simp [b.zero_of_le_dist (le_of_lt (lt_of_not_ge h))]
    unfold f p; simp only; rw [b.one_of_mem_closedBall,ofReal_one,one_mul]
    rw [mem_closedBall_zero_iff,Real.norm_of_nonneg ht.1]; exact ht.2

variable {K : Set E} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [IsLocallyFiniteMeasure μ] [SigmaFinite μ] [FiniteDimensional ℝ X]
variable {f : ℂ×(X×Y) → ℂ} {p : E → Y} {w : E × ℂ → ℂ}
section cert
lemma cauchy_average (hu : IsOpen U) (hf : AH U f) (hp : Continuous p) (hc : IsCompact K)
    (hw : ContinuousOn w (K ×ˢ U)) (hV : ∀ a∈K,DifferentiableOn ℂ (fun s=> w (a,s)) U) :
    AH U (fun x:ℂ×X=> ∫ v in K,w (v,x.1)*f (x.1,(x.2,p v)) ∂μ) := by
    apply locate; intro c hC
    obtain ⟨r,hr,h⟩:= Metric.mem_nhds_iff.mp (hu.mem_nhds hC)
    let R:=r/2; have hR :0<R:=half_pos hr; let u:= ball c R;let k (t):=circleMap c R t
    have ht : closedBall c R⊆U:= Subset.trans (closedBall_subset_ball (half_lt_self hr)) h
    have hg (t:ℝ): k t∈ U:= ht (sphere_subset_closedBall (circleMap_mem_sphere c hR.le t))
    obtain ⟨L,hL,hL'⟩:=get_kernel (c:=c) hR
    let F (b:ℂ×(X×(Y×ℝ))):= L (b.1,b.2.2.2)*f (b.1,(b.2.1,b.2.2.1))
    have H:AH u F:= (hL.arguments (by fun_prop : HasTemperateGrowth (fun y:X×(Y×ℝ)=> y.2.2))).mul ((hf.arguments (by fun_prop : HasTemperateGrowth (fun y:X×(Y×ℝ)=> (y.1,y.2.1)))).upon (ball_subset_closedBall.trans ht))
    let d:ℂ:= (2:ℂ)* ↑Real.pi*I; have hd0:d ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
    let a:= K ×ˢ Θ; have hcomp: IsCompact a:= hc.prod isCompact_Icc
    let ν:Measure (E×ℝ):=(μ.prod volume).restrict a
    let W (v:E×ℝ):=d⁻¹ * deriv k v.2 * w (v.1,k v.2);let q(v:E×ℝ):=(p v.1,v.2)
    have hq : Continuous q:= hp.comp continuous_fst|>.prodMk continuous_snd
    have hj : ContinuousOn W a:= by
       refine (continuousOn_const.mul (?_)).mul (hw.comp ?_ fun x hx=> ?_)
       · exact (((by apply contDiff_infty_iff_deriv.mp (contDiff_circleMap ..)|>.2 : ContDiff ℝ ∞ (deriv k)).continuous).comp continuous_snd).continuousOn
       · exact (continuous_fst.prodMk ((continuous_circleMap ..).comp continuous_snd)).continuousOn
       exact ⟨hx.1,hg _⟩
    have hT : Integrable W ν:= hj.integrableOn_compact hcomp
    have hs:AH u (fun x:ℂ×X=> ∫ v,W v*F (x.1,x.2,q v) ∂ν):= H.after_average hT (hq.aestronglyMeasurable) ((ae_restrict_mem (μ:=μ.prod volume) hcomp.measurableSet).mono (fun x hx=> mem_image_of_mem q hx)) (hcomp.image hq)
    refine ⟨u,mem_ball_self hR,hs.congr isOpen_ball ?_⟩
    intro z hz x
    have hl(v) (hv:v∈K): (∫ θ:ℝ in Θ, W (v,θ)*L (z,θ))=w (v,z):=by
       have he:= ((hV v hv).mono ht).circleIntegral_sub_inv_smul (show z∈ball c R from hz)
       rw [circleIntegral_def_Icc] at he; simp_rw [smul_eq_mul] at he
       calc
        _ = d⁻¹*( d * w (v,z)):= by
            change _=d⁻¹* ((2 * (↑Real.pi:ℂ) * I)*_); rw [← he,← integral_const_mul]; refine setIntegral_congr_fun measurableSet_Icc fun t hh=> ?_
            unfold W; dsimp only; rw [hL' z t hh]; dsimp only [d,k]; ring
        _ = _:=inv_mul_cancel_left₀ hd0 _
    change ∫ v in a,W v*F (z,x,q v) ∂(μ.prod volume)=_
    rw [setIntegral_prod]
    · refine setIntegral_congr_fun hc.measurableSet fun v hv=> ?_; change ∫ θ in Θ, W _ * (L _* f (z,x,p v))= w (v,z)*_; simp_rw [← mul_assoc]; rw [integral_mul_const]; exact congr_arg (· *_ ) (hl v hv)
    exact (hj.mul ((H.slice hz).1.continuous.comp (continuous_const.prodMk hq)).continuousOn).integrableOn_compact hcomp
end cert
end AH
end YM.MSbar.Symbol
