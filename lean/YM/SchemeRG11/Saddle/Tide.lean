import YM.SchemeRG11.Saddle.Gleam
import YM.SchemeRG11.Saddle.Weigh
/-! Faddeev determinant along the slice, pointwise tangent calculus. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.SchemeRG11.Sway
open scoped Classical ContDiff Topology Matrix.Norms.Frobenius
open Function Filter Lattice Pert.Orb PertExtension.Orb LocalH MeasureTheory Precision Push.Loops
variable {G:Gauge}{n:Side}{E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def rake(x h:E)(t:ℝ):= x+t • h
lemma rake_rate(x h:E): HasDerivAt (rake x h) h 0:=by simpa only [one_smul] using! (((hasDerivAt_id' (0:ℝ)).smul_const h).const_add x)
lemma rake_run{U:Type*}[NormedAddCommGroup U][NormedSpace ℝ U]{f:E→ U}{x:E}(hf:DifferentiableAt ℝ f x)(h:E): HasDerivAt (fun t=> f (rake x h t)) (fderiv ℝ f x h) 0:= by
 have he:=hf.hasFDerivAt
 have he': HasFDerivAt f (fderiv ℝ f x) (rake x h 0):= by simpa [rake] using he
 exact he'.comp_hasDerivAt 0 (rake_rate x h)

def Pulse {G:Gauge}(f:ℝ→ G.El)(t:ℝ)(v:G.Color):Prop:= HasDerivAt (fun t=> G.mat (f t)) (G.colorMat v * G.mat (f t)) t
lemma Pulse.change {f g:ℝ→ G.El}{t:ℝ}{v:G.Color}(H:Pulse f t v) (ht:f=ᶠ[𝓝 t]g):Pulse g t v:= by
 unfold Pulse; rw [← ht.eq_of_nhds]; exact H.congr_of_eventuallyEq (ht.symm.mono (fun i hi=> congrArg G.mat hi))
lemma Pulse.times {f g:ℝ→ G.El}{t:ℝ}{v u:G.Color}(H:Pulse f t v)(K:Pulse g t u):Pulse (fun s=> f s*g s) t (v+ G.adjoint (f t) u):= by
 have ht:=H.mul K; unfold Pulse
 simp only [G.mat_mul,Gauge.mat_adjoint,Gauge.conjugate,map_add,add_mul]; apply ht.congr_deriv; simp [mul_assoc,← mul_assoc (star (G.mat (f t))) (G.mat (f t))]
lemma Pulse.oppos {f:ℝ→ G.El}{t:ℝ}{v:G.Color}(H:Pulse f t v): Pulse (fun s=>(f s)⁻¹) t (-G.adjoint ((f t)⁻¹) v):=by
 have h:=H.star; unfold Pulse; refine h.congr_deriv ?_; simp [G.colorMat_skew,Gauge.conjugate,mul_assoc]
lemma Pulse.three {f g k:ℝ→ G.El}{t:ℝ}{v u w:G.Color}(H:Pulse f t v)(K:Pulse g t u)(L:Pulse k t w):Pulse (fun s=> f s*g s* (k s)⁻¹) t (v+ G.adjoint (f t) u -G.adjoint (f t*g t*(k t)⁻¹) w):= by
 simpa only [map_neg,← G.adjoint_mul, sub_eq_add_neg] using ((H.times K).times L.oppos)
lemma Pulse.const (u:G.El)(t:ℝ):Pulse (fun _=>u) t 0:=by unfold Pulse; rw [map_zero,zero_mul]; exact hasDerivAt_const ..
lemma Pulse.exact {f:ℝ→ G.El}{t:ℝ} (h:ContDiffAt ℝ ω (fun s=> G.mat (f s)) t): Pulse f t (deriv (fun s=>delta (f t) (f s)) t):=by
 let g(s:ℝ):= delta (f t) (f s)
 have he : Tendsto f (𝓝 t) (𝓝 (f t)):= tendsto_mat.mpr h.continuousAt.tendsto
 have hv:=he.eventually (bump_delta (f t))
 have hd: HasDerivAt g (deriv g t) t:= ((delta_diff contDiffAt_const h rfl).differentiableAt (by simp)).hasDerivAt
 have hp: HasFDerivAt (fun a=> G.mat (G.lieExp a)) (G.colorMat.toContinuousLinearMap) (g t):= by rw [show g t=0 from delta_self _]; exact G.expDiff_zero
 have hm:= (hp.comp_hasDerivAt t hd).mul_const (G.mat (f t))
 exact hm.congr_of_eventuallyEq (hv.mono fun i hi=> (congrArg G.mat hi).symm)
lemma Pulse.readout {x:E}{f:E→ G.El}(h: ContDiffAt ℝ ω (fun z=> G.mat (f z)) x)(a:E): Pulse (f ∘ rake x a) 0 (fderiv ℝ (fun z=>delta (f x) (f z)) x a):=by
 have he:= rake_run (f:=fun z=>delta (f x) (f z)) ((delta_diff contDiffAt_const h rfl).differentiableAt (by simp)) a
 have hk:= Pulse.exact (f:=f ∘ rake x a) (t:=0) (by
    have hJ: rake x a 0 = x:=by simp [rake]
    exact (show ContDiffAt ℝ ω (fun z=> G.mat (f z)) (rake x a 0) from hJ.symm ▸ h).comp 0 (show ContDiffAt ℝ ω (rake x a) 0 from contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)))
 rw [← he.deriv]; simpa only [comp_apply,show rake x a 0=x from by simp [rake]] using hk
lemma Pulse.draw {x:E}{f:E→ G.Color}(h: ContDiffAt ℝ ω f x)(a:E): Pulse (fun t=>G.lieExp (f (rake x a t))) 0 (theta (f x) (fderiv ℝ f x a)):=by
 have he:= Pulse.readout (f:=G.lieExp ∘ f) (G.exp_jet.contDiffAt.comp x h) a
 have hf: fderiv ℝ (fun z=>delta (G.lieExp (f x)) (G.lieExp (f z))) x = (theta (f x)).comp (fderiv ℝ f x):= fderiv_comp x ((theta_diff (f x)).differentiableAt (by simp)) (h.differentiableAt (by simp))
 change Pulse _ 0 (fderiv ℝ (fun z=>delta (G.lieExp (f x)) (G.lieExp (f z))) x a) at he
 rw [hf] at he; exact he
lemma Pulse.links {x:E}{f:E→ Potential G n}(h: ContDiffAt ℝ ω f x)(a:E)(l): Pulse (fun t=> positiveLinks (f (rake x a t)) l) 0 (theta ((f x).val l) ((fderiv ℝ f x a).val l)):=by
 let L:= (takeLink (G:=G) l).toContinuousLinearMap
 have he:= draw (L.contDiff.contDiffAt.comp (f:=f) x h) a
 rw [fderiv_comp x L.differentiableAt (h.differentiableAt (by simp)), L.fderiv] at he; exact he
lemma Pulse.unique {f:ℝ→ G.El}{t:ℝ}{v u:G.Color}(h:Pulse f t v)(g:Pulse f t u):v=u:= HasDerivAt.unique (delta_rate h) (delta_rate g)

def atVertical(v: Potential G n): Parameter G n→L[ℝ] Potential G n:= fderiv ℝ (shiftedLog v) 0
lemma entry_rate:∀ᶠ v:Potential G n in 𝓝 0, ∀ z:Parameter G n, dLin (atVertical v z)= FPDeriv v z ∧ ∀ l:Pert.Orb.Links n,
 theta (v.val l) ((atVertical v z).val l)=z.val l.1- G.adjoint (positiveLinks v l) (z.val (l.1+step l.2)):=by
 have ht: Tendsto (fun v:Potential G n=>(v,(0:Parameter G n))) (𝓝 0) (𝓝 0):= tendsto_id.prodMk_nhds tendsto_const_nhds
 filter_upwards [shift_static (G:=G) (n:=n),ht.eventually ((shift_smooth (G:=G) (n:=n)).eventually (by simp)),ht.eventually (eventually_eventually_nhds.mpr shift_exact)] with v hv hd he
 let f:= shiftedLog v
 have hg : ContDiffAt ℝ ω f 0 := ContDiffAt.comp (g:=fun p:Potential G n × Parameter G n=>shiftedLog p.1 p.2) (f:=fun z=>(v,z)) 0 hd (contDiffAt_const.prodMk contDiffAt_id)
 let D: Potential G n→L[ℝ] ↥(Flow G n):= dLin.toContinuousLinearMap
 have hm : FPDeriv v = D.comp (atVertical v):= ((D.hasFDerivAt.comp 0 (hg.differentiableAt (by simp)).hasFDerivAt).fderiv)
 intro z; rw [hm]; refine ⟨rfl,fun l=>?_⟩
 have hb:=Pulse.links hg z l
 have hw : (fun t=>positiveLinks (f (rake 0 z t)) l)=ᶠ[𝓝 (0:ℝ)] fun t=>turn v (rake 0 z t) l:=by
    have hh:Tendsto (fun t:ℝ=>(v,rake (0:Parameter G n) z t)) (𝓝 0) (𝓝 (v,0)):=tendsto_const_nhds.prodMk_nhds (by simpa [rake] using! (rake_rate (0:Parameter G n) z).continuousAt.tendsto)
    exact (hh.eventually he).mono fun i hi=> congrFun hi l
 have hh(x:Site n): Pulse (fun t=>G.lieExp ((rake 0 z t).val x)) 0 (z.val x):=by
    unfold Pulse; dsimp only; rw [show (fun t : ℝ=>G.mat (G.lieExp ((rake 0 z t).val x)))= (fun t=> G.mat (G.lieExp (t • z.val x))) from funext fun t=> by rw [rake,zero_add];rfl,show rake 0 z 0=0 by simp [rake],show G.mat (G.lieExp ((0:Parameter G n).val x))=1 by simp,mul_one]; apply line_diff
 rw [show f 0=v from hv] at hb
 apply Pulse.unique (hb.change hw); convert (hh l.1).three (Pulse.const (positiveLinks v l) 0) (hh (l.1+step l.2)) using 1 <;>
 first | rfl | simp [rake]

end YM.SchemeRG11.Sway
