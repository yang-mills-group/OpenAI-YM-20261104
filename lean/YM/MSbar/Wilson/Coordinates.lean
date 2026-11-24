import YM.Gauge.Chart
import YM.Gauge.Casimir
import Mathlib

/-!
# Neighbourhood vector fields from actual two-sided gauge action. Wilson
perturbative tangent defined with Frobenius ambient, not guessed universal
coefficient of a log. Handles disconnected Gauge and source ghosts with
chosen orthonormal convention. Bracket law pointwise on a neighbourhood (uses
image immersion and symmetry of second derivative). Not just finite jet cap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Native.Chart
open Function Filter Set Gauge NormedSpace MeasureTheory
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius NNReal
variable (G:Gauge)
local notation "A"=> G.Color
abbrev Rail (G:Gauge):=G.Color × G.Color
noncomputable def Up : A→ G.Mat:= G.mat ∘ G.lieExp
noncomputable def hit (b:Rail G)(t:ℝ)(x:A): G.El:= G.lieExp (t • (-b.1))* G.lieExp x* G.lieExp (t • b.2)
noncomputable def head (b:Rail G)(p:ℝ × A): A:= G.plog (G.mat (hit G b p.1 p.2))
noncomputable def speed (b:Rail G)(x:A): A:= fderiv ℝ (head G b) (0,x) (1,0)
lemma still (b:Rail G)(x:A): hit G b 0 x=G.lieExp x:=by simp [hit]
lemma jet (b:Rail G):ContDiffAt ℝ ω (head G b) (0,0):=by
   have hf:ContDiff ℝ ω (fun p:ℝ×A=> G.mat (hit G b p.1 p.2)):= by
       let L:=fun x=> G.mat (G.lieExp x)
       have he: (fun p:ℝ× A=> G.mat (hit G b p.1 p.2))= fun p=> L (p.1 • (-b.1))*L p.2 * L (p.1 • b.2):= by funext x; simp only [hit,G.mat_mul,L]
       rw [he]; apply ContDiff.mul
       · exact (ContDiff.mul (G.exp_jet.comp (contDiff_fst.smul contDiff_const)) (G.exp_jet.comp contDiff_snd))
       exact G.exp_jet.comp (contDiff_fst.smul contDiff_const)
   unfold head; refine ContDiffAt.comp (g:=G.plog) (0,0) ?_ hf.contDiffAt; rw [still,G.mat_lieExp_zero,G.mat_one]; exact G.plog_diff
lemma speeds (b:Rail G):ContDiffAt ℝ ω (speed G b) 0:= ((jet G b).fderiv_right (m:=ω) (by simp)|>.clm_apply (g:=fun _=> (1,0)) contDiffAt_const).comp (f:=fun x:A=>((0:ℝ),x)) 0 (by fun_prop)
lemma enters (b:Rail G):∀ᶠ x:A in 𝓝 0, head G b (0,x)=x:= by simp only [head,still]; exact G.plog_left
lemma down (b: Rail G): ∀ᶠ p:ℝ×A in 𝓝 (0,0), G.lieExp (head G b p)=hit G b p.1 p.2:= by
   let f(p: ℝ×A):=hit G b p.1 p.2
   have hp:Continuous f:=by
      unfold f hit; refine Continuous.mul (Continuous.mul ?_ ?_) ?_
      · exact G.lieExp_cont.comp (continuous_fst.smul continuous_const)
      · exact G.lieExp_cont.comp continuous_snd
      exact G.lieExp_cont.comp (continuous_fst.smul continuous_const)
   have he:f (0,0)=1:=by simp [f, still]
   have hv : Tendsto f _ _ := hp.tendsto (0,0);rw [he] at hv;exact hv.eventually G.plog_right

lemma armed : ∀ᶠ i:A in 𝓝 0, Injective (fderiv ℝ (Up G) i) := by
    filter_upwards [(EventuallyEq.fderiv (𝕜:=ℝ) (show G.plog ∘ Up G =ᶠ[𝓝 0] id from G.plog_left)), ((show Tendsto (Up G) (𝓝 0) (𝓝 1) from by have he:= G.exp_jet.continuous.tendsto 0; simpa [Up,-mat_lieExp] using! he).eventually (G.plog_diff.eventually (by simp)))] with y hy hv
    rw [fderiv_comp y (hv.differentiableAt (by simp)) (G.exp_jet.differentiable (by simp) y), fderiv_id] at hy
    exact (show LeftInverse (fderiv ℝ (G.plog) (Up G y)) (fderiv ℝ (Up G) y) from fun x=> DFunLike.congr_fun hy x).injective
lemma hits (b:Rail G)(x:A) : HasDerivAt (fun t:ℝ=>G.mat (hit G b t x)) (-(G.colorMat b.1)*Up G x + Up G x*G.colorMat b.2) 0 := by
    have he(a:A): HasDerivAt (fun t:ℝ=> Up G (t • a)) (G.colorMat a) 0:= by
       simp only [Up,Function.comp_apply,G.mat_lieExp,map_smul]; simpa using! hasDerivAt_exp_smul_const (G.colorMat a) (0:ℝ)
    have hv:= ((he (-b.1)).mul_const (Up G x)).mul (he b.2)
    rw [show (fun t:ℝ=>G.mat (hit G b t x))= (fun t:ℝ=> Up G (t • (-b.1))* Up G x)*(fun t=> Up G (t • b.2)) from funext fun t=>by simp only [hit,G.mat_mul];rfl]; simpa only [Up, zero_smul, Function.comp_apply, G.mat_lieExp_zero,G.mat_one,mul_one,one_mul,map_neg] using! hv

-- helper head_speed
lemma breeze (b:Rail G)(x:A)(h:ContDiffAt ℝ ω (head G b) (0,x)): HasDerivAt (fun t:ℝ=> head G b (t,x)) (speed G b x) 0:=by
    exact ((h.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (0:ℝ) ((hasDerivAt_id' (0:ℝ)).prodMk (hasDerivAt_const _ x)))
lemma follows (b:Rail G): ∀ᶠ i:A in 𝓝 0, fderiv ℝ (Up G) i (speed G b i)= -G.colorMat b.1 * Up G i + Up G i * G.colorMat b.2 := by
    have hp:= ((continuous_const (y:=(0:ℝ))).prodMk continuous_id).tendsto (0:A) -- spec
    have hf : Tendsto (fun y:A=> ((0:ℝ),y)) (𝓝 0) (𝓝 ((0:ℝ),(0:A))) := hp
    filter_upwards [enters G b,hf.eventually ((jet G b).eventually (by simp)), hf.eventually (eventually_eventually_nhds.mpr (down G b))] with x h i u
    have hg:= ((show DifferentiableAt ℝ (Up G) (head G b (0,x)) from by apply G.exp_jet.differentiable (by simp)).hasFDerivAt.comp_hasDerivAt (0:ℝ) (breeze G b x i)); rw [h] at hg
    refine (hg.congr_of_eventuallyEq ?_).unique (hits G b x); filter_upwards [((continuous_id.prodMk (continuous_const (y:=x))).tendsto (0:ℝ)).eventually u] with p hp
    exact (congr_arg (G.mat) hp).symm
lemma begins (b:Rail G): speed G b 0=b.2-b.1:=by
    have he:=(follows G b).self_of_nhds; have h:= G.expDiff_zero.fderiv; change fderiv ℝ (Up G) _=_ at h; rw [h, show Up G 0=1 by simp [Up], mul_one,one_mul] at he; apply G.colorMat_injective;rw [map_sub]; change G.colorMat _ =_ at he; rw [he]; abel

-- Jacobi normalizer law of charts. commute derivatives after pushing into Group
noncomputable def bracket (G:Gauge)(v b:Rail G):Rail G := (G.ad v.1 b.1, G.ad v.2 b.2)
private lemma floated (b: Rail G): ∀ᶠ x:A in 𝓝 0,∀ v:A,
       fderiv ℝ (fderiv ℝ (Up G)) x v (speed G b x)+fderiv ℝ (Up G) x (fderiv ℝ (speed G b) x v) = - G.colorMat b.1 * fderiv ℝ (Up G) x v + fderiv ℝ (Up G) x v * G.colorMat b.2:=by
   filter_upwards [(show (fun i=> fderiv ℝ (Up G) i (speed G b i))=ᶠ[𝓝 0] _ from follows G b).fderiv (𝕜:=ℝ),(speeds G b).eventually (by simp)] with x p h v
   let D:= fderiv ℝ (Up G)
   have he := (((show ContDiffAt ℝ ω (Up G) x from G.exp_jet.contDiffAt).fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)).hasFDerivAt.clm_apply ((h.differentiableAt (by simp)).hasFDerivAt)
   have hv: DifferentiableAt ℝ (Up G) x:= G.exp_jet.differentiable (by simp) x
   have hm:= hv.hasFDerivAt; have hx:= (HasFDerivAt.mul' (hasFDerivAt_const (-G.colorMat b.1) _) hm).add (HasFDerivAt.mul' hm (hasFDerivAt_const (G.colorMat b.2) _));
   have heq:= (he.fderiv).symm.trans (Eq.trans p (show _ from hx.fderiv)); have hp:= DFunLike.congr_fun heq v
   simp at hp
   change fderiv ℝ (Up G) x _ + fderiv ℝ (fderiv ℝ (Up G)) x v _ =-(G.colorMat b.1*fderiv ℝ (Up G) x v) + 0*Up G x+(Up G x * 0+fderiv ℝ (Up G) x v*G.colorMat b.2) at hp; rw [zero_mul,mul_zero,add_zero,zero_add] at hp;rw [add_comm,hp,neg_mul]

lemma rhythm (a b:Rail G):∀ᶠ i:A in 𝓝 0,
     fderiv ℝ (speed G b) i (speed G a i) - fderiv ℝ (speed G a) i (speed G b i) = speed G (bracket G a b) i:=by
    filter_upwards [follows G b,follows G a,follows G (bracket G a b),armed G,floated G b,floated G a] with i p q f e g h
    have he:=g (speed G a i); have hp:= h (speed G b i); rw [show fderiv ℝ (fderiv ℝ (Up G)) i (speed G a i) (speed G b i)=fderiv ℝ (fderiv ℝ (Up G)) i (speed G b i) (speed G a i) from (show ContDiffAt ℝ ω (Up G) i from G.exp_jet.contDiffAt).isSymmSndFDerivAt_of_omega .., q] at he; rw [p] at hp;
    apply e;rw [map_sub, f, eq_sub_of_add_eq' he,eq_sub_of_add_eq' hp]; simp only [bracket,colorMat_ad];noncomm_ring
end YM.MSbar.Native.Chart
