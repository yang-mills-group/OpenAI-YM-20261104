import YangMills.WilsonProof.NativeSupport.YM.MS.Bare.Shadows
import YM.MS.Bare.MixD

/-!
# Haar divergence price for formal Taylor germs

Including constant modes retained on bare finite mesh (not inversion ray test).
 Point BB. Haar parameter never changes with UV. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Bare.Maurer
open Function Filter Set LocalH Mix Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge}
abbrev base (G : Gauge): Module.Basis G.ColorIndex ℝ (C G):= (EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis
def divs (F:C G→C G)(a:C G) := tab (base G) (fderiv ℝ F a)
lemma by_row (F:C G → C G)(a:C G): divs F a=∑ i:G.ColorIndex, fderiv ℝ F a (base G i) i := by unfold divs; rw [tab_trace]; simp [base]

section left
variable (x:C G)
def path (x:C G)(t:ℝ)(v:C G) := move G (G.lieExp (-(t • x))) v
lemma remembered (t:ℝ)(v:C G): path x t v= G.plog (G.mat (step (x,0) v t)):= by unfold path step move snap; rw [smul_zero,G.mat_lieExp_zero,mul_one]

variable {U:Set G.El}{s:Set (C G)}(H:Geom G U s){a:C G}(h:a∈s)
include H h
lemma path_begin : path x 0 a=a:= by rw [remembered,step_start]; exact snap_on H h
lemma path_d : ContDiffAt ℝ ω (uncurry (path x)) (0,a):= by
    have he : ContDiff ℝ ω (fun z : ℝ × C G=> G.mat (G.lieExp (-(z.1 • x))* G.lieExp z.2)):= by simp only [G.mat_mul]; exact (G.exp_jet.comp (contDiff_fst.smul contDiff_const|>.neg)).mul (G.exp_jet.comp contDiff_snd)
    refine (show ContDiffAt ℝ ω G.plog _ from ?_).comp (f:=fun z : ℝ × C G=>G.mat (G.lieExp (-(z.1 • x)) * G.lieExp z.2)) _ he.contDiffAt
    dsimp only; rw [zero_smul,neg_zero,G.mat_lieExp_zero,one_mul]; exact analytic_here H h
lemma path_dir : HasDerivAt (fun t:ℝ=> path x t a) (volts (x,0) a) 0 := by
    simp_rw [remembered]; exact amp (x,0) H h
lemma path_dirx : fderiv ℝ (path x 0) a=1:= by
    have he : path x 0 =ᶠ[𝓝 a] id:= Eventually.mono (H.2.1.mem_nhds h) (fun a ha=> path_begin x H ha)
    exact (hasFDerivAt_id a).congr_of_eventuallyEq he|>.fderiv -- one
lemma mixed_unit : fderiv ℝ (fun t:ℝ=> fderiv ℝ (path x t) a) 0 1=fderiv ℝ (volts (x,0)) a:= by
    apply ContinuousLinearMap.ext; intro v; rw [cap_mix (path x) (0:ℝ) a 1 v (path_d x H h)]
    have hv : (fun y=> fderiv ℝ (fun t:ℝ=> path x t y) 0 1) =ᶠ[𝓝 a] volts (x,0):= by
       filter_upwards [H.2.1.mem_nhds h] with y hy; rw [(path_dir x H hy).hasFDerivAt.fderiv]; simp
    rw [hv.fderiv_eq]

lemma left_div (hu:(1:G.El)∈U)(ha:0<spin G a): divs (volts (x,0)) a+ fderiv ℝ (lac (G:=G)) a (volts (x,0) a)=0:= by
    let Y (t:ℝ) := fderiv ℝ (path x t) a; have hh : Y 0=1:= path_dirx x H h;
    obtain ⟨he,hZ⟩:= tableau 0 (base G) Y (gradright (path x) 0 a (path_d x H h)) hh
    let Ω t := (Y t).det
    have h1 : Ω 0=1:= by simp only [Ω,hh]; exact map_one LinearMap.det -- maybe simp one
    have hΩ : HasDerivAt Ω (divs (volts (x,0)) a) 0:= by
        have hh : HasDerivAt Ω (fderiv ℝ Ω 0 1) 0:= (he.differentiableAt (by simp)).hasFDerivAt.hasDerivAt
        rwa [show fderiv ℝ Ω 0 1=_ from hZ 1,show fderiv ℝ Y 0 1=_ from mixed_unit x H h] at hh
    have hv : (fun t=> spin G (path x t a)*Ω t) =ᶠ[𝓝 0] fun _=>spin G a:= by
       filter_upwards [walk_on (x,0) H h] with t hT; apply spins G H hu a; change step (x,0) a t∈ U at hT; simpa [step] using hT
    have hm : HasDerivAt (fun t=> spin G (path x t a)) (fderiv ℝ (spin G) a (volts (x,0) a)) 0:= HasFDerivAt.comp_hasDerivAt_of_eq (f:=fun t:ℝ=>path x t a) 0 ((spin_deriv G a).differentiableAt (by simp)).hasFDerivAt (path_dir x H h) (path_begin x H h).symm
    have hz := ((hm.mul hΩ).congr_of_eventuallyEq hv.symm).unique (hasDerivAt_const 0 (spin G a))
    rw [path_begin x H h,h1] at hz; have hu : lac (G:=G)=Real.log ∘ spin G:= rfl
    rw [hu,fderiv_comp _ (Real.differentiableAt_log ha.ne') ((spin_deriv G a).differentiableAt (by simp)),ContinuousLinearMap.comp_apply,(Real.hasDerivAt_log ha.ne').hasFDerivAt.fderiv]; change divs _ a + fderiv ℝ (spin G) a (volts (x,0) a)*(spin G a)⁻¹=0; field_simp; linarith
end left

lemma left_0 (x:C G): ∀ᶠ a:C G in 𝓝 0, divs (volts (x,0)) a+ fderiv ℝ (lac (G:=G)) a (volts (x,0) a)=0:= by
    obtain ⟨r,hr,H⟩:= geom_patch G
    filter_upwards [ball_mem_nhds (0:C G) hr, lives G] with a h hR; exact left_div x (H r (le_refl r)) h ⟨0,mem_ball_self hr,G.mat_lieExp_zero⟩ hR
lemma negative_turn (x:C G): ∀ᶠ a:C G in 𝓝 0, divs (volts (0,x)) a+ fderiv ℝ (lac (G:=G)) a (volts (0,x) a)=0:= by
    let l := volts (x,0); let u:= volts (0,x); let n := (-1:Mix.J (C G)); have hG : n= - ContinuousLinearMap.id ℝ (C G):= rfl
    have hx : Tendsto n (𝓝 0) (𝓝 0):= by simpa using n.continuous.tendsto 0
    have hl : ∀ᶠ a in 𝓝 0, ContDiffAt ℝ ω (lac (G:=G)) (n a) ∧ ContDiffAt ℝ ω l (n a) := hx.eventually (((hlog G).eventually (by simp)).and ((home (x,0)).eventually (by simp)))
    have he : (lac (G:=G) ∘ n)=ᶠ[𝓝 0] lac:= opposite
    have hw : (n ∘ l ∘ n)=ᶠ[𝓝 0] u:= by
       filter_upwards [volt_back (0,x)] with a h; change -l (-a)= u a; change l (-a)= -u a at h; rw [h,neg_neg]
    filter_upwards [hl,hw,hw.fderiv (𝕜:=ℝ), he.fderiv (𝕜:=ℝ), hx.eventually (left_0 x)] with a ha hh h hU hp
    change divs u a+_=0; unfold divs; rw [← show fderiv ℝ (n ∘ l ∘ n) a= fderiv ℝ u a from h, ← show n (l (n a))=volts (0,x) a from hh,← show fderiv ℝ (lac∘ n) a= fderiv ℝ lac a from hU];
    have hv : DifferentiableAt ℝ l (n a) := ha.2.differentiableAt (by simp)
    rw [fderiv_comp a n.differentiableAt (hv.comp _ n.differentiableAt),fderiv_comp a hv n.differentiableAt,fderiv_comp a (ha.1.differentiableAt (by simp)) n.differentiableAt,n.fderiv,n.fderiv]; unfold divs at hp; simp only [hG, ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id,ContinuousLinearMap.id_comp, neg_neg, neg_apply,ContinuousLinearMap.id_apply,map_neg] -- maybe many unused
    exact hp
lemma wind_div (x:Ends G): ∀ᶠ a:C G in 𝓝 0, divs (volts x) a+ fderiv ℝ lac a (volts x a)=0:= by
    rcases x with ⟨u,v⟩; filter_upwards [left_0 u,negative_turn v,(home (u,0)).eventually (by simp), (home (0,v)).eventually (by simp)] with a ha hb he hh; have hx : volts (u,v) = volts (u,0)+volts (0,v):= funext fun a=> by unfold volts; simp only [Pi.add_apply, ← map_add,Prod.mk_add_mk,add_zero,zero_add]
    simp_rw [by_row] at *; rw [hx,fderiv_add (he.differentiableAt (by simp)) (hh.differentiableAt (by simp)), Pi.add_apply,map_add]; simp only [add_apply,PiLp.add_apply, Finset.sum_add_distrib]; linarith
end YM.MS.Bare.Maurer
