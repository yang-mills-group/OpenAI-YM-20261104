import YM.OPE.Compatible.Soup.Yore
/-!
# Sharp Pen uniform at every chamber-exterior input
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant.Aloof
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Set
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal
open Eyrie Push.Mark Cascade
variable {G:Gauge}{b i j k r:ℕ}{n:Side}
local notation "K!"=> Palace G r
local notation "F!"=> Config G n
variable (hp:Board n (r+1)) (φ:lots G n)(hf:Continuous φ)
include hf
private lemma boundedΦ :∃ c:ℝ,∀ x, ‖φ x‖≤c:=by obtain ⟨a,ha,H⟩:= isCompact_univ.exists_isMaxOn (show (univ:Set F!).Nonempty from ⟨1,mem_univ _⟩) hf.norm.continuousOn; exact ⟨_,fun v=> H (mem_univ v)⟩
lemma silentC : Continuous (innC hp φ):=by
       obtain ⟨c,hc⟩:=boundedΦ φ hf; exact continuous_of_dominated (fun i=>(hf.comp (monoInst hp i)).aestronglyMeasurable) (fun i=>Eventually.of_forall (fun v=>hc _)) (integrable_const c) (Eventually.of_forall fun v:K!=> hf.comp ((Cinst hp).comp (f:=fun i:F! => (i,v)) (by fun_prop)))
lemma fig (p:lots G n)(he:LocalOn (Outer r 0) p)(hM:Envelope p): πfee (innC hp φ) p= πfee φ p:=by
       let μ:=prior G n; let ν:= Duo G r; let f : F!× K!→ℂ:=fun i=>φ (move hp i.1 i.2)*p i.1; let g:F!→ℂ:=fun i=> φ i*p i
       have hh (i:K!) : MeasurePreserving (fun U=>move hp (G:=G) U i) μ μ:=measurePreserving_pi (f:=fun j u=>u*(install hp 1 i) j) _ _ fun i=> measurePreserving_mul_right G.probHaar _
       have hs (i) : (∫ U:F!, f (U,i) ∂μ)=πfee φ p:=by
           have hg : Measurable g:= hf.measurable.mul hM.meas; have hz:= integral_map (hh i).aemeasurable (f:=g) hg.aestronglyMeasurable -- parameter
           rw [(hh i).map_eq] at hz; change _= ∫ x,g x ∂μ; rw[hz]; exact integral_congr_ae (Eventually.of_forall fun x=> congr_arg ((φ (move hp x i))*·) (he _ _ (private_q hp x i)))
       obtain ⟨a,hA⟩:=boundedΦ φ hf; obtain ⟨b,hb⟩:=hM.cost; have hC:Continuous (fun i:F!×K!=> φ (move hp i.1 i.2)):= hf.comp (continuous_fst.mul ((monoInst hp (1:F!)).comp continuous_snd)); have hF:Integrable f (μ.prod ν):= Integrable.of_bound (show Measurable f from hC.measurable.mul (hM.meas.comp measurable_fst)).aestronglyMeasurable (a*b) (Eventually.of_forall fun i=> (norm_mul ..).trans_le (mul_le_mul (hA _) (hb i.1) (norm_nonneg _) ((norm_nonneg _).trans (hA i.1))))
       change (∫ U, innC hp φ U*p U ∂μ)= _; simp_rw [bent hp φ hf, ← integral_mul_const]; change (∫ U,∫ v,f (U,v) ∂ν ∂μ)=_; rw [← integral_prod _ hF,integral_prod_symm _ hF]; simp only [hs,integral_const,probReal_univ,one_smul]
private lemma epsC {K:Set (Site n)}{t:ℝ} (h:LocalOn K φ)(hv:∀ p:lots G n,LocalOn K p→ Envelope p→‖πfee φ p‖ ≤ t*γfee p)(x:F!):‖φ x‖ ≤ t:=by
       suffices H:∀ ε:ℝ,0<ε →‖φ x‖≤ t+ε by by_contra hp; have hg: t<‖φ x‖:=lt_of_not_ge hp; have hz:= H ((‖φ x‖-t)/2) (by linarith only [hg]); linarith only [hz,hg]
       intro ε hε; let s: Set F!:= {y|‖φ x-φ y‖ < ε}; have hs:IsOpen s:= isOpen_lt ((continuous_const.sub hf).norm) continuous_const; have hx:x∈ s:=(by simp[s,hε]); let p:= s.indicator (fun _=> (1:ℂ)); have hh := hs.measurableSet
       have hp: Envelope p:=⟨measurable_const.indicator hh,1,fun i=>by by_cases h:i∈s <;>simp [p,h]⟩ -- indentation
       have hU:LocalOn K p:= by intro U V ht; unfold p; unfold s; simp only [Set.indicator,mem_setOf_eq,h _ _ ht]
       let μ := prior G n; let B:=μ.real s; haveI : Measure.IsOpenPosMeasure μ := by unfold μ prior; infer_instance
       have hm:0 < B:=ENNReal.toReal_pos (hs.measure_pos _ ⟨x,hx⟩).ne' (measure_ne_top _ _)
       have hz: πfee φ p= ∫ i in s, φ i ∂μ:=by rw[← integral_indicator hh]; unfold πfee; exact integral_congr_ae (Eventually.of_forall fun i=> by by_cases h:i∈s <;>simp [p,h])
       have hX: γfee p=B:=by
             change (∫ i, ‖p i‖ ∂μ)=_; rw [← show (∫ i in s,(1:ℝ)∂μ)=B from by simp [B],←integral_indicator hh]; exact integral_congr_ae (Eventually.of_forall (fun i=>by by_cases h:i∈s <;> simp [p,h]))
       have hZ := norm_setIntegral_le_of_norm_le_const (μ:=μ) (s:=s) (measure_lt_top _ _) (f:=fun i=>φ x-φ i) (C:=ε) fun i h=>(show _< ε from h).le
       rw[integral_sub (integrable_const _) ((hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).integrableOn), setIntegral_const,← hz] at hZ
       apply le_of_mul_le_mul_right _ hm; calc
            _ = ‖B • φ x‖:=by rw [norm_smul_of_nonneg hm.le]; exact mul_comm ..
            _ ≤ ‖B • φ x-πfee φ p‖+‖πfee φ p‖:=by nth_rw 1[← sub_add_cancel (B • φ x) (πfee φ p)]; exact norm_add_le ..
            _ ≤ ε*B+t*B:= add_le_add hZ (hX ▸ hv p hU hp)
            _ = _:= by ring
lemma punt (h:GaugeInvariant φ)(b:ℝ) (hu:∀ p:lots G n, LocalOn (Outer r 0) p → Envelope p→ ‖πfee φ p‖ ≤ b*γfee p)(x:F!): ‖innC hp φ x‖≤ b:=epsC (innC hp φ) (silentC hp φ hf) (innGI hp φ hf h) (fun p he hx=> (fig hp φ hf p he hx).symm ▸ hu p he hx) x -- simp freeze
end YM.OPE.Merchant.Aloof
