import YM.Trace.Fock.Regularity
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Bare light-shell branch identities imply singleton spatial support of bounded-order
Cauchy jets, via vacuum locality on product tests. No existence of charged field words in the
image is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 1200
namespace YM.Trace.Shell
open YM Boundary Function Set Filter MeasureTheory Complex
open scoped Topology ENNReal BigOperators InnerProductSpace ContDiff
variable {s : ℕ} (f : Probe Mom)
def shape (g : ℝ→ℂ) (x : E4) := f (spatial x) * g (time x)
lemma adjoint_divide_preserve : MeasurePreserving Mink.divide.symm volume volume := MeasurePreserving.symm Mink.divide.toHomeomorph.toMeasurableEquiv Mink.volume_divide
@[fun_prop] lemma smooth_shape {g} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (shape f g) := by
     exact ((f.smooth _).comp Mink.restL.contDiff).mul (hg.comp Mink.clockL.contDiff) -- definition Schwartz
lemma shape_support (g) : tsupport (shape f g) ⊆ Mink.divide ⁻¹' (tsupport f ×ˢ tsupport g) := closure_minimal (by
   rintro i hi; rw [Set.mem_preimage, Set.mem_prod, Mink.divide_at]; exact ⟨Classical.byContradiction (fun h => hi (by simp only [shape,image_eq_zero_of_notMem_tsupport h, zero_mul])),
   Classical.byContradiction (fun h=> hi (by simp only [shape,image_eq_zero_of_notMem_tsupport h,mul_zero]))⟩) (isClosed_closure.prod isClosed_closure|>.preimage Mink.divide.continuous)
lemma shape_compact (hf : CC f) {g} (h : HasCompactSupport g) : HasCompactSupport (shape f g) := by
    exact (Mink.divide.toHomeomorph.isClosedEmbedding.isCompact_preimage (hf.prod h)).of_isClosed_subset isClosed_closure (shape_support f g)
noncomputable def productProbe (g : ℝ→ℂ) (hf : CC f) (h : ContDiff ℝ ∞ g) (hg : HasCompactSupport g) :=
    (shape_compact f hf hg).toSchwartzMap (smooth_shape f h)
lemma plane_split (g) (x : Mom × ℝ) (e : ℝ) (p r : Mom) : let z := YM.position x.1 x.2; Probe.plane z (YM.position p ((e:ℝ) * ‖r‖)) * shape f g z =
     (Probe.plane x.1 p * f x.1) * ((timePhase r (e*x.2)) * g x.2) := by
      intro z; simp_rw [shape, timePhase,Probe.plane,Mink.pairing]
      simp only [z,time_position,spatial_position]; push_cast; rw [add_mul, exp_add]; ring

lemma intPlane (q : E4) {f : Test4} (hf : CC f) : Integrable (fun x:E4 => Probe.plane x q * f x) volume := ((by unfold Probe.plane; fun_prop : Continuous (fun x:E4=> Probe.plane x q)).mul f.continuous).integrable_of_hasCompactSupport
    (show HasCompactSupport (fun x => Probe.plane x q * (f x)) from HasCompactSupport.smul_left (f:=fun x=>Probe.plane x q) hf)
lemma factorPlane (g : ℝ→ℂ) (hf : CC f) (h : ContDiff ℝ ∞ g) (hg : HasCompactSupport g) (e : ℝ) (r : Mom) : let p := e • r
     plus (productProbe f g hf h hg) (YM.position p (e*‖r‖)) = plus f p * ∫ t:ℝ, (timePhase r (e*t)) * g t := by
   intro p
   rw [plus_eq,plus_eq,← MeasureTheory.integral_const_mul, ← adjoint_divide_preserve.integral_comp (Mink.divide.symm|>.toHomeomorph.measurableEmbedding)]
   erw [integral_prod_symm (μ:=(volume:Measure Mom)) (ν:=(volume:Measure ℝ)) _]
   · refine integral_congr_ae (ae_of_all _ fun t=> ?_)
     change _=(∫ x : Mom,Probe.plane x p*f x)*(timePhase r _ * g t)
     rw [← MeasureTheory.integral_mul_const]; exact integral_congr_ae (ae_of_all _ fun y=> plane_split f g (y,t) e p r)
   have HQ := adjoint_divide_preserve.integrable_comp_emb (Mink.divide.symm|>.toHomeomorph.measurableEmbedding) (g:=fun x => Probe.plane x (YM.position p (e*‖r‖)) * productProbe f g hf h hg x)
   exact HQ.mpr (intPlane _ (f:=productProbe f g hf h hg) (by exact shape_compact f hf hg))

lemma temporal_factor (g hf hg h p) : let fE := productProbe f g hf hg h;
    Probe.hat fE (ray p) = Probe.hat f p * ∫ t:ℝ, timePhase p (-t)*g t := by
    intro fE; have hm : -ray p=YM.position ((-1:ℝ) • p : Mom) ((-1:ℝ)*‖p‖) := Mink.ext_by (by simp:_) (by simp : _)
    have ht : Probe.hat fE (ray p)=plus fE (-ray p) := by rw [plus_eq_hat,neg_neg]
    rw [ht,hm]
    have hq := factorPlane f g hf hg h (-1:ℝ) p; refine hq.trans ?_; simp [plus_eq_hat]
lemma temporal_pos (g hf hg h p) : let fE:= productProbe f g hf hg h;
    plus fE (ray (-p)) = Probe.hat f p * ∫ t:ℝ,timePhase p t *g t := by
    intro fE; have hm : ray (-p)=YM.position ((1:ℝ) • (-p) : Mom) ((1:ℝ)*‖-p‖) := Mink.ext_by (by simp) (by simp)
    have hq := factorPlane f g hf hg h 1 (-p); rw [hm]; refine hq.trans ?_; simp [timePhase,plus_eq_hat]


lemma empty_time_neighborhood (hf : CC f) (hO : (0:Mom)∉tsupport f) : ∃ ε>0, ∀ r∈tsupport f, (ε:ℝ) < ‖r‖ := by
   obtain H|⟨r,hI⟩ := (tsupport f).eq_empty_or_nonempty
   · refine ⟨1,zero_lt_one,?_⟩; simp [H]
   obtain ⟨z,hz,ht⟩ := hf.exists_isMinOn ⟨r,hI⟩ continuous_norm.continuousOn
   have hm : ‖z‖ > 0 := norm_pos_iff.mpr (by rintro rfl; exact hO hz)
   exact ⟨‖z‖/2,half_pos hm, fun i hi => (half_lt_self hm).trans_le (ht hi)⟩

variable {A D : Mom→ℂ} (h : Control s A) (h' : Control s D)
abbrev Rule (A B : Mom→ℂ) := ∀ φ : Test4, Eligible φ → (∫ p, Probe.hat φ (ray p)*A p∂ν) = ∫ r, plus φ (ray r)*B r∂ν
lemma probe_exchange (hx : Rule A D) (hf : CC f) (hO : (0:Mom)∉tsupport f) {g : ℝ→ℂ} (hg : ContDiff ℝ ∞ g) (hgd : HasCompactSupport g) {ε:ℝ}
     (he : ∀ r∈tsupport f, ε<‖r‖) (het : tsupport g ⊆ Ioo (-ε) ε) :
     (∫ r, (Probe.hat f r * ∫ t, timePhase r (-t)*g t) * A r ∂ν) = ∫ r, (Probe.hat f r * ∫ t, timePhase r t*g t) * D (-r) ∂ν := by
      let ψ := productProbe f g hf hg hgd
      have H' (H:Eligible ψ) : _ := hx ψ H -- adjust
      refine Eq.trans (by simp_rw [← temporal_factor f g hf hg hgd]; rfl : _=(∫ r, Probe.hat ψ (ray r)*A r∂ν)) ((H' ?_).trans ?_)
      swap
      · rw [← integral_neg_eq_self (fun p=> plus ψ (ray p) * D p) ν]; simp only [ψ,temporal_pos f g hf hg hgd]
      refine ⟨by exact shape_compact f hf hgd, fun x hx=>?_⟩
      have hm := shape_support f g hx
      exact (Mink.lateral x).mpr (abs_lt.mpr (het hm.2) |>.trans (he _ hm.1))

lemma factorize_phase (e : Bool) (f : Probe Mom) (g : ℝ→ℂ) (hg : Continuous g) (hc : HasCompactSupport g) {A : Mom→ℂ} {N : ℕ} (h : Control N A) : let k (t:ℝ) := if e then -t else t
    (∫ r, (f r * ∫ t, timePhase r (k t)*g t)*A r ∂ν) = ∫ t, (∫ r, timePhase r (k t)*(f r) * A r ∂ν)*g t := by
      intro k; let U := fun r (t:ℝ) => (timePhase r (k t)* f r) * A r * g t
      have ht : Continuous k := by unfold k; split_ifs <;> fun_prop
      have hmic : Continuous (fun p : Mom × ℝ => timePhase p.1 (k p.2)) := by unfold timePhase; fun_prop
      have hJ : Integrable (uncurry U) (ν.prod (volume:Measure ℝ)) :=
         ((h.leg_regular f|>.1).mul_prod (hg.integrable_of_hasCompactSupport hc)).mono
            (((hmic.mul (f.continuous.comp continuous_fst)).aestronglyMeasurable.mul h.ae.comp_fst).mul (hg.comp continuous_snd|>.aestronglyMeasurable)) (.of_forall fun z => by simp only [uncurry,U,norm_mul,phase_norm,one_mul,Pi.mul_apply,le_rfl])
      simp_rw [show ∀ r, f r * (∫ t, timePhase r (k t)*g t) = _ from fun r=> (MeasureTheory.integral_const_mul ..).symm,
         ← MeasureTheory.integral_mul_const]
      exact Eq.trans (integral_congr_ae (.of_forall fun r=> integral_congr_ae (.of_forall fun t=>show _=U r t from by unfold U; ring))) (integral_integral_swap (f:=U) hJ)


end YM.Trace.Shell
