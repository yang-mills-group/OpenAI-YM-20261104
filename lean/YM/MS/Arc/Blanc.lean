import YM.MS.Arc.Opp
import Mathlib.Analysis.Complex.Schwarz
/-!
# Bounded holomorphic on right half-plane: a Blaschke extraction

Division by any factor from the positive real axis preserves the already
 normalized bound, no number of derivatives. With gamma-removed integrals. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real Metric
open scoped Topology ContDiff Interval
variable {F:Type}[NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F]
def right0 : Set ℂ := {z|0<z.re}
lemma right_open : IsOpen right0:=by unfold right0; exact isOpen_lt continuous_const Complex.continuous_re

def runP (n:ℝ)(z:ℂ): ℂ:= (z - n)/(z+n)
def logP (n:ℝ)(z:ℂ): ℂ:= (n:ℂ) * (1+ z)/(1-z)
variable {n:ℝ}{z:ℂ}
lemma Ynum (p:ℂ): p.re^2+p.im^2=‖p‖^2:= by simpa [Complex.normSq_apply,pow_two] using (Complex.sq_norm p).symm -- sq_norm
lemma stag (hn:0<n)(hz:z∈right0): z+(n:ℂ)≠0:= fun h=> by
   have he : z.re + n=0:= by convert congr_arg Complex.re h <;> simp
   have hp:0<z.re:= hz; linarith
lemma Aster (hn:0<n)(h: z∈right0): runP n z ∈ ball 0 1:= by
   unfold runP; rw [mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.mpr (stag hn h))]; have hp:0<z.re:=h; have ht:=Ynum (z-n); have he:= Ynum (z+n); simp only [Complex.sub_re, Complex.add_re,Complex.ofReal_re,Complex.sub_im, Complex.add_im,Complex.ofReal_im,sub_zero,add_zero] at ht he; nlinarith [norm_nonneg (z+(n:ℂ)),norm_nonneg (z-(n:ℂ))]
lemma Subunit (h : z ∈ ball 0 1): 1 - z≠0:= fun he=> by
    replace he : z=1:= (sub_eq_zero.mp he).symm; simp_all
lemma Knick (hn:0<n)(h: z∈ ball 0 1): logP n z∈ right0:= by
   have hi : 0 < ‖1-z‖:= norm_pos_iff.mpr (Subunit h)
   have he:= Ynum z; have ht := mem_ball_zero_iff.mp h; unfold right0; rw [mem_setOf]; unfold logP
   rw [Complex.div_re]; simp only [Complex.sub_re, Complex.sub_im,Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im, Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]; simp only [zero_mul, sub_zero,add_zero,zero_add,zero_sub]; rw [← Complex.sq_norm]; field_simp; rw [zero_mul]; apply mul_pos hn; nlinarith [norm_nonneg z]
lemma erased (hn:0<n)(h:z∈right0): logP n (runP n z)=z:= by
   unfold logP runP; have he : 1-runP n z≠0:= Subunit (Aster hn h); have hp:= stag hn h; unfold runP at he; have hu : (n:ℂ)≠0:= Complex.ofReal_ne_zero.mpr hn.ne'; rw [div_eq_iff he]; field_simp; ring -- simpler
-- a one zero
variable {f: ℂ→F}{C:ℝ}
omit [CompleteSpace F] in
lemma discount (h:Forest right0 f)(hv:∀ i∈right0,‖f i‖≤ C)(hn:0<n)(hp:f n=0)(x:ℂ)(he:x∈right0) : ‖f x‖≤ C*‖runP n x‖:= by
   let X:= f ∘ logP n; let Z:= ball (0:ℂ) 1; have hm: X 0=0:= by simp [X,logP,hp]
   have HX : DifferentiableOn ℂ X Z:= by
       intro z hz; have he : 1-z≠0:= Subunit hz; exact (DifferentiableAt.comp z (h _ (Knick hn hz)) (show DifferentiableAt ℂ (logP n) z by unfold logP; fun_prop (disch:=assumption))).differentiableWithinAt -- disch
   have hQ : MapsTo X Z (closedBall (X 0) C):= fun i hi=> by rw [hm]; simpa only [mem_closedBall, dist_zero_right,X,Function.comp_apply] using (hv _ (Knick hn hi))
   obtain hi:= Complex.dist_le_div_mul_dist_of_mapsTo_ball HX hQ (Aster hn he); simpa only [hm, dist_zero_right,X,Function.comp_apply,erased hn he,div_one] using hi
omit [CompleteSpace F] in
lemma thin (h:z∈right0)(hm:0<n)(hn:z≠(n:ℂ)): runP n z≠0:= div_ne_zero (sub_ne_zero.mpr hn) (stag hm h)
lemma mop (h:Forest right0 f)(hv:∀ i∈right0,‖f i‖≤C)(hn:0<n)(hp:f n=0): ∃ G:ℂ→F, Forest right0 G∧ (∀ z∈right0,‖G z‖≤C)∧ (∀ z∈right0,f z=runP n z • G z):= by
   let G z:= (z+(n:ℂ)) • dslope f (n:ℂ) z; let Z:ℂ:= (n:ℝ); have hz: Z∈right0:=hn
   have hm : Forest right0 G:= fun x hx=> ((show DifferentiableAt ℂ (fun z=>z+Z) x by fun_prop).smul ((Complex.differentiableOn_dslope (right_open.mem_nhds hz)).mpr (fun x hx=> (h x hx).differentiableWithinAt) _ hx|>.differentiableAt (right_open.mem_nhds hx))) -- name
   have he x (hx:x∈right0): runP n x • G x=f x:= by
       by_cases hv:x=(n:ℂ); · subst x; simp [runP,hp]
       unfold G runP; rw [dslope_of_ne _ hv,slope_def_module,hp,sub_zero,smul_smul, div_mul_cancel₀ _ (stag hn hx),smul_inv_smul₀ (sub_ne_zero.mpr hv)] -- rw
   have hB z (hz:z∈right0)(hh:z≠Z): ‖G z‖≤C:= by
       obtain hδ:= discount h hv hn hp z hz; rw [← he z hz, norm_smul,mul_comm C] at hδ; exact le_of_mul_le_mul_left hδ (norm_pos_iff.mpr (thin hz hn hh))
   refine ⟨G,hm,fun z hz'=>?_ ,fun z hz=> (he z hz).symm⟩; rcases eq_or_ne z Z with rfl|hx; swap; · exact hB z hz' hx -- subst Z maybe z
   refine le_of_tendsto ((hm _ hz').continuousAt.norm.continuousWithinAt (s:={(n:ℂ)}ᶜ)) ?_; filter_upwards [show right0∈𝓝[≠] Z from nhdsWithin_le_nhds (right_open.mem_nhds hz),self_mem_nhdsWithin] with t ht ht'; exact hB t ht ht'
end YM.MS.Arc
