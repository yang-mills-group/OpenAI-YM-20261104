import YM.Trace.Fock.Chart
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
/-! Absence of negative powers; chart boundary numerator. -/
noncomputable section
set_option maxHeartbeats 600000
set_option autoImplicit false
namespace YM.Trace.Shell
open Function Set YM Filter Boundary Complex MeasureTheory Measure
open scoped Pointwise Topology BigOperators ENNReal ContDiff
lemma dense_shell {P : Mom→Prop} (h : ∀ᵐ p∂ν, P p) : ∀ᵐ p∂(volume:Measure Mom), P p := by
 have he := ae_withDensity_iff (μ:=(volume:Measure Mom)) (f:=ENNReal.ofReal ∘ scalarWeight) (ENNReal.measurable_ofReal.comp scalar_meas)|>.mp h
 filter_upwards [show ∀ᵐ p:Mom, p ≠ 0 from ae_iff.mpr (by simp),he] with p hp hh
 exact hh (show ENNReal.ofReal _ ≠0 from (ENNReal.ofReal_pos.mpr (inv_pos.mpr (show 0<2*‖p‖ by exact mul_pos zero_lt_two (norm_pos_iff.mpr hp)))).ne')
instance shell_open_pos : ν.IsOpenPosMeasure := ⟨fun U h he hU=> (h.measure_pos volume he).ne' (id (by simpa using ae_iff.mp (dense_shell (P:=fun p=>p∉U) (ae_iff.mpr (by simpa using hU))) : volume U=0))⟩
instance cord_open_pos (n : ℕ) : (νpow n).IsOpenPosMeasure := inferInstanceAs (IsOpenPosMeasure (Measure.pi (fun _: Fin n=>ν)))

def band (δ : ℝ) (p : Mom) := (Ioo 0 δ).indicator (fun r=> (r^2)⁻¹) ‖p‖
@[fun_prop] lemma band_meas (δ : ℝ) : Measurable (band δ) := (((measurable_id.pow_const 2).inv.indicator measurableSet_Ioo) |>.comp measurable_norm)
lemma band_nonnegative (δ p) : 0 ≤ band δ p := indicator_nonneg (fun _ _=>inv_nonneg.mpr (sq_nonneg _)) _
lemma band_infinite {δ : ℝ} (hδ : 0 < δ) : ¬ Integrable (band δ) ν := by
 rw [shell_integrable_iff]
 let f (r:ℝ) := (2*r)⁻¹ * (Ioo 0 δ).indicator (fun r:ℝ=> (r^2)⁻¹) r
 change ¬ Integrable (fun p:Mom=> f ‖p‖)
 rw [integrable_fun_norm_addHaar (volume:Measure Mom) (f:=f)]
 intro hg
 apply (lt_irrefl (-1:ℝ)) ((intervalIntegral.integrableOn_Ioo_rpow_iff (s:=-1) hδ).mp _)
 refine IntegrableOn.congr_fun ((hg.mono_set (Ioo_subset_Ioi_self)).const_mul 2) ?_ measurableSet_Ioo
 intro r hr;  have : Module.finrank ℝ Mom = 3 := by simp [Mom,YM.Space3,YM.SpaceAxis]
 change _ * (r ^ (Module.finrank ℝ Mom -1) * f r)=_; rw [this]; norm_num; change 2*(r^2*f r) = _
 unfold f; rw [indicator_of_mem hr,Real.rpow_neg_one]; field_simp [hr.1.ne']

private lemma singular_at (h : Mom→ℂ) (f : Mom→ℝ) (hc : Continuous h) (hi : Integrable (fun x=>(f x)^2) ν) (C : ℝ) (hC : 0 ≤ C) (he : ∀ᵐ x∂ν, ‖x‖ < 1 → ‖h x‖ ≤ ‖x‖ * (C * f x)) : h 0=0 := by
 by_contra hk
 let a := ‖h 0‖/2
 have ha : 0<a := half_pos (norm_pos_iff.mpr hk)
 obtain ⟨δ,hδ,H⟩:= Metric.continuousAt_iff.mp (hc.norm.continuousAt (x:=0)) a ha
 let d := min 1 δ
 have hyp (x : Mom) (hx : ‖x‖ < d) : a ≤ ‖h x‖ := by
     have he := H (show dist x 0 < δ from (lt_of_lt_of_le (by simpa using hx : _<d) (min_le_right ..)))
     simp only [Real.dist_eq] at he; have := (abs_lt.mp he).1; dsimp only [a] at *; linarith
 apply band_infinite (show 0<d from lt_min zero_lt_one hδ) ((show Integrable ((C/a)^2 • (fun p:Mom => (f p)^2)) ν by exact hi.const_mul _).mono' (band_meas d|>.aestronglyMeasurable) ?_)
 refine he.mono (fun x hx=> ?_)
 change ‖band d x‖ ≤ _; rw [Real.norm_eq_abs,_root_.abs_of_nonneg (band_nonnegative ..)]
 by_cases hxx : ‖x‖∈Ioo 0 d
 · have e := (hyp x hxx.2).trans (hx (hxx.2.trans_le (min_le_left ..)))
   have L : ‖x‖⁻¹ ≤ C / a * f x := by
     rw [inv_le_iff_one_le_mul₀ hxx.1,div_mul_eq_mul_div,div_mul_eq_mul_div,le_div_iff₀ ha,one_mul]; rw [mul_comm]; exact e
   unfold band; rw [indicator_of_mem hxx,← inv_pow]; change ‖x‖⁻¹ ^2 ≤ (C / a)^2 * ((f x)^2); rw [← mul_pow]; exact pow_le_pow_left₀ (inv_pos.mpr (norm_pos_iff.mpr (norm_pos_iff.mp hxx.1))|>.le) L _
 unfold band; rw [indicator_of_notMem hxx]; change 0 ≤ (C/a)^2*(f x)^2; positivity

variable {n m : ℕ}
@[fun_prop] lemma join_cont (i : Fin (n+1)) : Continuous (join i) := continuous_pi_iff.mpr fun j=> by
 by_cases h : j=i; · subst j; exact (continuous_congr (fun _=>join_pos _ _)).mpr continuous_fst
 rcases Fin.exists_succAbove_eq_iff.mpr h with ⟨b,rfl⟩
 exact (continuous_congr (fun _=>join_expose ..)).mpr ((continuous_apply _).comp continuous_snd)
lemma mill_join (i : Fin (n+1)) (x : Mom×Cords n) : mill (join i x)=‖x.1‖*mill x.2 := by
 unfold mill; rw [Fin.prod_univ_succAbove (fun j:Fin (n+1)=>‖join i x j‖) i]; simp_rw [join_pos,join_expose]
lemma norm_join (i : Fin (n+1)) (p : Mom) (y : Cords n) (h : ‖p‖≤1) : ‖join i (p,y)‖ ≤ 1+‖y‖ := by
 rw [pi_norm_le_iff_of_nonneg (G:=fun _:Fin (n+1)=>Mom) (by positivity)]; intro j
 by_cases hj:j=i; · subst j; rw [join_pos]; simp only; linarith [norm_nonneg y]
 obtain ⟨z,rfl⟩:=Fin.exists_succAbove_eq_iff.mpr hj
 simpa only [join_expose] using (le_of_lt (by linarith [norm_le_pi_norm y z] : ‖y z‖<1+‖y‖))
variable (v:Test4→L[ℂ] Sum m) (hv : FieldImage v) (k : @Angle m (n+1)) {q : ℕ}
include hv
lemma foot_vanish (i : Fin (n+1)) (c : chartIdx q (n+1)→ℂ) (hc : smoothBody v k=ᶠ[ae (νpow (n+1))] chartValue c): ∀ y:Cords n, chartValue c (join i (0,y))=0 := by
 let U (p:Cords (n+1)) := ‖fullWave v (n+1) p‖
 let P (x:Mom × Cords n) := chartValue c (join i x)
 obtain ⟨l,hl⟩:=tempered_Lp v hv (n+1)
 let f (x:Mom×Cords n) := U (join i x)/((1+‖join i x‖)^l)
 have hi : Integrable (fun x=> (f x)^2) (ν.prod (νpow n)) := (join_preserving i|>.integrable_comp_emb (g:=fun x:Cords (n+1) => (‖fullWave v (n+1) x‖ / (1+‖x‖)^l)^2) (join i|>.measurableEmbedding))|>.2 (by simpa only [Real.norm_eq_abs,sq_abs] using! (memLp_two_iff_integrable_sq_norm hl.aestronglyMeasurable).mp hl)
 have hm : ∀ᵐ y:Cords n∂νpow n, P (0,y)=0 := by
     have hE : ∀ᵐ y∂νpow n, ∀ᵐ x∂ν, smoothBody v k (join i (x,y))=P (x,y) := Measure.ae_ae_comm (α:=Mom) (β:=Cords n) (μ:=ν) (ν:=νpow n) (p:=fun x y=> smoothBody v k (join i (x,y))=P (x,y)) ?_|>.mp (Measure.ae_ae_of_ae_prod (p:=fun z=>smoothBody v k (join i z)=P z) (join_preserving i|>.quasiMeasurePreserving.ae hc))
     swap; · exact (measurableSet_eq_fun (f:=fun x:Mom×Cords n=>smoothBody v k (join i x)) (by fun_prop) (g:=P) (by unfold P; fun_prop))
     filter_upwards [hi.prod_left_ae,hE] with y hInt hE
     let W (x:Mom):Mom×Cords n := (x,y)
     refine singular_at (P ∘ W) (f ∘ W) (((chartValue_cont c).comp (join_cont _)).comp (by unfold W; fun_prop)) hInt (mill y * (2+‖y‖)^l) (by have := nonnegative_mill y; positivity) (hE.mono (fun x (hx:smoothBody v k _=_) hL=> ?_))
     rw [comp_apply,← hx]
     unfold smoothBody; rw [norm_mul,norm_real,Real.norm_of_nonneg (nonnegative_mill ..),mill_join,mul_assoc]
     change ‖x‖ * _ ≤ _
     apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
     have hLT : ‖fullWave v (n+1) (join i (x,y)) k‖ ≤ (2+‖y‖)^l * f (W x) := by
        let s := join i (x,y)
        have ht : 2+‖y‖>0 := by positivity
        have he := PiLp.norm_apply_le (fullWave v _ s) k
        refine he.trans ?_
        dsimp [f,W]; change U s ≤ (2+‖y‖)^l * _
        rw [← mul_div_assoc,le_div_iff₀ (by positivity)]
        rw [mul_comm (U _)]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by have := norm_join i x y hL.le; simpa only [s] using show 1+‖join i (x,y)‖ ≤ 2+‖y‖ by linarith) _) (norm_nonneg _)
     rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hLT (nonnegative_mill _)
 have hc : Continuous (fun y=> P ((0:Mom), y)) := by unfold P; exact (chartValue_cont c).comp ((join_cont i).comp (continuous_const.prodMk continuous_id))
 exact congrFun ((hc.ae_eq_iff_eq _ continuous_zero).mp (show (fun y=> P ((0:Mom),y))=ᶠ[ae (νpow n)] (0 : Cords n→ℂ) from hm))
end YM.Trace.Shell
