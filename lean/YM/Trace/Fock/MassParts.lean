import YM.Trace.Fock.Beams
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace YM.Trace.Shell
open Complex YM MeasureTheory Function Filter Set Boundary
open scoped Pointwise BigOperators ENNReal Topology InnerProductSpace
variable {m q n : ℕ} (f : Test4) (c : chartIdx q n→ℂ)
abbrev cell (n : ℕ) := MeasureTheory.Lp ℂ 2 (νpow n)
noncomputable def beamLip (h : highCap c) (i : ℕ) : cell n := (beam_memLp c f h i).toLp (fun p => plus f (total p) * sectionFunc c i p) -- h no inference
noncomputable def rawSeries (t : ℝ) (p) := ∑ i∈degrees q n, ((↑(t^(n+i)):ℂ) * (plus f (total p)) * sectionFunc c i p)
noncomputable def linePoly (s : Finset ℕ) (n : ℕ) (w : ℕ→cell n) (t : ℝ) := ∑ i∈s, (t^(n+i):ℝ) • w i
lemma beamLip_ae (h : highCap c) (i : ℕ): ⇑(beamLip f c h i) =ᶠ[ae (νpow n)] fun x=> plus f (total x)*sectionFunc c i x := (beam_memLp c f h i).coeFn_toLp
lemma linePoly_ae (h : highCap c) (t : ℝ) : (fun p:Cords n=> (linePoly (degrees q n) n (beamLip f c h) t) p)=ᶠ[ae (νpow n)] rawSeries f c t := by
 unfold linePoly beamLip rawSeries
 let w := beamLip f c h
 refine (Lp.coeFn_fun_finsetSum (degrees q n) (fun i=>(t^(n+i):ℝ) • w i)).trans ?_
 filter_upwards [(ae_all_iff.mpr fun i => ((Lp.coeFn_smul (t^(n+i):ℝ) (w i)).trans ((beamLip_ae f c h i).const_smul _)))] with x hx
 rw [Finset.sum_congr rfl (fun i _=>(hx i).trans (show _ = ((↑(t^(n+i)):ℂ)*_)*sectionFunc c i x by rw [Pi.smul_apply, real_smul]; rw [mul_assoc]))] -- fix hx

lemma raw_series_eq (h : highCap c) (t : ℝ) (ht : 0<t) : rawSeries f c t= fun p=> (↑(t^n):ℂ) * (plus f (total p) * release c (t • p)) := by
 funext p; simp only [section_sum,rawSeries, Finset.mul_sum,pow_add, section_smul c _ p ht h, ofReal_mul, ofReal_pow]; apply Finset.sum_congr rfl (fun i _=>by ring)
lemma lipNorm (x : cell n) : ‖x‖^2=∫ p, ‖x p‖^2∂νpow n := by
     have hg := congr_arg re (MeasureTheory.L2.inner_def (𝕜:=ℂ) x x)
     rw [← RCLike.re_to_complex, ← RCLike.re_to_complex, ← _root_.integral_re (MeasureTheory.L2.integrable_inner (𝕜:=ℂ) ..)] at hg
     simp only [inner_self_eq_norm_sq (𝕜:=ℂ)] at hg; exact hg
lemma linePoly_normSq (h : highCap c) (t : ℝ) : ‖linePoly (degrees q n) n (beamLip f c h) t‖^2 = ∫ p,‖rawSeries f c t p‖^2∂νpow n := (lipNorm _).trans (integral_congr_ae ((linePoly_ae f c h t).mono (fun x (hx: _ =rawSeries _ c t x)=> by dsimp only at hx ⊢; rw [hx])))

def componentFn (k : @Angle m n) (v : Wave m n) : Cords n → ℂ := fun p => v p k
lemma componentIntegrable (v : Wave m n) (k) : Integrable (fun p:Cords n=> ‖componentFn k v p‖^2) (νpow n) := by
     refine (memLp_two_iff_integrable_sq_norm ?_).mp (MemLp.of_le (Lp.memLp v) ?_ (.of_forall (fun x=> PiLp.norm_apply_le ..))) <;> exact (PiLp.continuous_apply ..).comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)
variable (v : Test4→L[ℂ] Sum m) (hv : FieldImage v) (k : @Angle m n)
include hv
lemma rawSeries_cell {t : ℝ} (ht : t>0) (hf : CC f) (h : highCap c) (hw : ∀ᵐ x ∂νpow n, fullWave v n x k = release c x) :
   rawSeries f c t =ᶠ[ae (νpow n)] fun x=> ((t^n:ℝ):ℂ)*(componentFn k (v (normalized f t) n) (t • x)) := by
   rw [raw_series_eq f c h _ ht]
   filter_upwards [(dilation_ae ht).ae (fullWave_of_CC v hv (normalized f t) (normalized_CC hf t) n),(dilation_ae ht).ae hw] with x hx hy
   unfold componentFn; rw [hx,total_smul ht,plus_normalized f ht, inv_smul_smul₀ ht.ne', PiLp.smul_apply, hy,smul_eq_mul]

lemma linePoly_component {t : ℝ} (hf : CC f) (h : highCap c) (hw : ∀ᵐ x ∂νpow n, fullWave v n x k = release c x) (ht : t>0) :
    ‖linePoly (degrees q n) n (beamLip f c h) t‖^2 = ∫ p, ‖componentFn k (v (normalized f t) n) p‖^2∂νpow n := by
    rw [linePoly_normSq]
    refine Eq.trans (integral_congr_ae (show _=ᶠ[ae _] (fun x=> ((t^n:ℝ)^2 * ‖componentFn k (v (normalized f t) n) (t • x)‖^2)) from (rawSeries_cell f c v hv k ht hf h hw).mono fun x (hx: rawSeries f c t x = (↑(t^n):ℂ)*(componentFn k (v (normalized f t) n) (t • x)))=> by dsimp only; rw [hx,norm_mul,norm_real,Real.norm_of_nonneg (by positivity),mul_pow])) ?_
    rw [MeasureTheory.integral_const_mul,generic_exchange (fun p=> ‖componentFn k (v (normalized f t) n) p‖^2) ht]; rw [← mul_assoc,← pow_mul, inv_pow, mul_comm 2 n, mul_inv_cancel₀ (pow_pos ht _|>.ne'),one_mul]
lemma linePoly_le {t : ℝ} (hf : CC f) (h : highCap c) (hw : ∀ᵐ x ∂νpow n, fullWave v n x k = release c x) (ht : t>0) :
   ‖linePoly (degrees q n) n (beamLip f c h) t‖ ≤ ‖v (normalized f t)‖ := by
   refine le_trans (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)|>.mp ?_) (show _ ≤ _ from lp.norm_apply_le_norm (show (2:ENNReal)≠0 by norm_num) (v (normalized f t)) n)
   let w := v (normalized f t) n
   rw [lp_sq w, linePoly_component f c v hv k hf h hw ht]
   exact integral_mono (componentIntegrable ..) (show Integrable (fun p:Cords n=>‖w p‖^2) _ from (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable w)).1 (Lp.memLp w)) (fun p=>pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le ..) _)
lemma assembled_sq (t) :
    ‖v (normalized f t) n‖ ^2 = ∑ k:@Angle m n, (∫ p, ‖componentFn k (v (normalized f t) n) p‖^2∂νpow n) := by
     let w := v (normalized f t) n; change ‖w‖^2 = _
     rw [lp_sq]; conv_lhs => enter [2,x]; rw [EuclideanSpace.norm_sq_eq]
     rw [(MeasureTheory.integral_finsetSum (f:=fun k : Angle (m:=m) (n:=n)=> fun p : Cords n=> ‖(w p) k‖^2) _ (μ:=νpow n) (by exact fun k _=>componentIntegrable w k))]; rfl
end YM.Trace.Shell
