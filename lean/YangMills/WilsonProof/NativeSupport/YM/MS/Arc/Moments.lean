import YangMills.WilsonProof.NativeSupport.YM.MS.Arc.Pumps
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
/-!
# Exact positive-integer control, on any Plot rapid

LW: empty power ℓ=0 cases. Not solving Mellin at poles here. Unit parameter pure, homogeneous exact rad moment values. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real Metric
open scoped Topology ContDiff Interval
variable {I E F G: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][CompleteSpace F]
variable {z:UScale I}{f:I→ Tree E F}{a:I→ℝ} {g:Tree E F}
-- package one-tree
abbrev Ultra (f:E×G→F) [NormedAddCommGroup G] [NormedSpace ℝ G]:= quiet 0 (fun _:Unit=> f) 1 -- need inst implicit before?
-- polynomial weighted
omit [CompleteSpace F] in
lemma slide (h:quiet z f a) (p:E)(i:I)(k m:ℕ): ∃ C:ℝ, 0<C∧∀ x:ℝ,‖x^k • f i (x,p)‖ ≤ C/(1+‖x‖)^m := by
   obtain ⟨C,hC,b,hb⟩:=Q.man h 0 (k+m); let V:=C*((1+|z i|)*(1+‖p‖))^b*a i; have ht : 0≤V:= by have hx:=Q.nonneg h i; unfold V; positivity
   refine ⟨1+V,by positivity,fun t=>?_⟩
   specialize hb i t p; simp only [norm_iteratedFDeriv_zero,pow_add] at hb; rw [norm_smul,norm_pow,le_div_iff₀ (by positivity), mul_comm _ ‖f i (t,p)‖, mul_assoc]; refine le_trans ?_ (hb.trans (le_add_of_nonneg_left zero_le_one)); gcongr; simp
omit [CompleteSpace F] in
lemma rolled (h: Ultra g)(p:E)(k:ℕ): Integrable (fun x:ℝ=> x^k • g (x,p)) (volume:Measure ℝ):= by
   obtain ⟨C,hC,hp⟩:= slide h p () k 2; have hz:= Reserve.dustInteg (S:=path fun x: Unit=>0) (μ:=volume) (E:=ℝ) () 2 (by simp); let W: ℝ→F:=fun x=> g (x,p); have hW: Continuous W := (h.smooth ()).continuous.comp (show Continuous (fun x:ℝ=> (x,p)) by fun_prop); refine (hz.const_mul C).mono' ((show Continuous fun x:ℝ=> x^k • W x by fun_prop).aestronglyMeasurable) (Eventually.of_forall fun x=>?_); simpa only [Scale.dust,Scale.weight,path,one_mul,div_eq_mul_inv] using hp x
omit [CompleteSpace F] in
lemma ended (h: Ultra g)(p:E)(k:ℕ): Tendsto (fun x:ℝ=> x^k • g (x,p)) atTop (𝓝 0):= by
   obtain ⟨C,hC,hp⟩:= slide h p () k 1; apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall fun x=> norm_nonneg _) ?_ (tendsto_const_nhds (x:=C)|>.div_atTop tendsto_id)
   filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht; apply (hp t).trans; simp only [pow_one,norm_of_nonneg ht.le]; apply div_le_div_of_nonneg_left hC.le ht; simp
-- Integration by parts
variable (h:Ultra g)(hm:Reflect g)
def vault (g:Tree E F)(p:E)(n:ℕ): F:= ∫ t,t^(2*n+1) • g (t,p) ∂μhalf
include h hm
lemma stairs (n:ℕ)(p:E): vault (chop g) p (n+1)= -(2*(n+1:ℝ)) • vault g p n := by
   let s:=2*n+1; have he: s+1= 2*(n+1):=by unfold s; omega
   have hx: ((s+1:ℕ):ℝ)=2*(n+1:ℝ):= by exact_mod_cast he
   let w(t:ℝ):= t^(s+1) • g (t,p); let L(t:ℝ):= t^(2*(n+1)+1) • chop g (t,p); let K(t:ℝ):= t^s • g (t,p); let f'(t:ℝ):= L t + ((s+1:ℕ):ℝ) • K t
   have hf (x:ℝ): HasDerivAt w (f' x) x:= by
       have hP:= ( (hasDerivAt_id' x).pow (s+1)).smul (dr (h.smooth ()) p x);
       convert! hP using 1
       unfold f' K L; rw [pow_succ _ (2*(n+1)),← he, mul_smul, restore hm (h.smooth ())]; simp [← smul_smul] -- expects factor hx
   have ht: Ultra (chop g):= Q.at_chop h (fun _=>hm); obtain hz:= (rolled ht p (2*(n+1)+1)).restrict (s:=Ioi 0); obtain hL := (rolled h p s).restrict (s:=Ioi 0)
   have HH := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _=> hf x) (show IntegrableOn f' _ _ from hz.add (hL.smul _)) (ended h p (s+1)); -- inspect syntax
   have h1 : (∫ t,L t ∂μhalf) + ((s+1:ℕ):ℝ) • (∫ t,K t ∂μhalf)=0:= ?_ -- parentheses wrong
   · rw [← hx,neg_smul]; exact eq_neg_of_add_eq_zero_left h1
   unfold f' w at HH; simp only [zero_pow (by omega : s+1≠0),zero_smul,sub_zero] at HH; rw [integral_add (show Integrable L (volume.restrict (Ioi 0)) from hz) (show Integrable (fun x=> ((s+1:ℕ):ℝ) • K x) (volume.restrict (Ioi 0)) from hL.smul ((s+1:ℕ):ℝ)), integral_smul] at HH; exact HH
lemma static (p:E): vault (chop g) p 0=-g (0,p):= by
   have he : Tendsto (fun t:ℝ=>g (t,p)) atTop (𝓝 0):=by simpa only [pow_zero,one_smul] using ended h p 0
   let Z(t:ℝ):= t^(2*0+1) • chop g (t,p); have hG (t:ℝ): Z t=d g (t,p):= by simpa only [Z,mul_zero,zero_add,pow_one] using restore hm (h.smooth ()) t p
   have hi:= integral_Ioi_of_hasDerivAt_of_tendsto' (a:=0) (f':=Z) (fun x _=> hG x ▸ dr (h.smooth ()) p x) ((rolled (Q.at_chop h (fun _=>hm)) p _).restrict) he; simpa only [Z,vault,μhalf,zero_sub] using hi
end YM.MS.Arc
