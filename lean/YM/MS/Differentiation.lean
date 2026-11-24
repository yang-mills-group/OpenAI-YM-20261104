import YM.MS.Rapid
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Iterating actual, not within-parameter, Bochner integrals on all momentum jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS
open Function Filter Set MeasureTheory Module
open scoped Topology ContDiff
variable {G W E F α : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup E] [NormedSpace ℝ E]
   [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [MeasurableSpace α]

/-- Slice-wise μ version. No topological structure on scale parameters in α needed. -/
structure Majorant (μ : Measure α) (f : α → E → F) : Prop where
   smooth : ∀ᵐ i ∂μ, ContDiff ℝ ∞ (f i)
   borel (j : ℕ) p : AEStronglyMeasurable (fun i => iteratedFDeriv ℝ j (f i) p) μ
   major (j : ℕ) (p : E) : ∃ v ∈ 𝓝 p, ∃ a : α → ℝ, Integrable a μ ∧ ∀ᵐ i ∂μ, ∀ q ∈ v, ‖iteratedFDeriv ℝ j (f i) q‖ ≤ a i

namespace Majorant
variable {μ : Measure α} {f : α → E → F} (h : Majorant μ f)
include h
lemma integ (j : ℕ) (p : E) : Integrable (fun i => iteratedFDeriv ℝ j (f i) p) μ := by
   obtain ⟨v,hv,a,ha,H⟩:= h.major j p; exact ha.mono' (h.borel j p) (H.mono fun i h=>h p (mem_of_mem_nhds hv))
lemma values (p : E) : Integrable (fun i=> f i p) μ := by
   let L : (E [×0]→L[ℝ] F) ≃L[ℝ] F := (continuousMultilinearCurryFin0 ℝ E F) -- check
   exact L.toContinuousLinearMap.integrable_comp (h.integ 0 p)
variable [CompleteSpace F]
lemma grad (p : E) (j : ℕ) :
    HasFDerivAt (fun q=> ∫ i, iteratedFDeriv ℝ j (f i) q ∂μ) (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => E) F (∫ i, iteratedFDeriv ℝ (j+1) (f i) p ∂μ)) p := by
   let H i := iteratedFDeriv ℝ j (f i)
   let L : (E [×(j+1)]→L[ℝ] F) ≃ₗᵢ[ℝ] (E →L[ℝ] (E [×j]→L[ℝ] F)) := continuousMultilinearCurryLeftEquiv ℝ _ _
   let D q i := L (iteratedFDeriv ℝ (j+1) (f i) q)
   obtain ⟨v,hv,a,ha,hB⟩:= h.major (j+1) p
   have hp : HasFDerivAt (fun q=> ∫ i, H i q ∂μ) (∫ i, D p i ∂μ) p := by
       refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F':=D) (F:=fun q i=>H i q) hv (.of_forall fun q=>(h.borel j q)) (h.integ j p) ?_ ?_ ha ?_
       exact L.continuous.comp_aestronglyMeasurable (h.borel (j+1) p)
       exact hB.mono (fun i h q hq=>by change ‖L _‖ ≤ _; rw [L.norm_map]; exact h q hq)
       exact h.smooth.mono fun i h q _=> (h.differentiable_iteratedFDeriv (m:=j) (by norm_cast; exact WithTop.coe_lt_top j) q).hasFDerivAt
   convert hp using 1
   let M : (E [×(j+1)]→L[ℝ] F) →L[ℝ] (E →L[ℝ] (E [×j]→L[ℝ] F)) := L.toContinuousLinearEquiv
   exact (ContinuousLinearMap.integral_comp_comm (𝕜:=ℝ) (E:= (E [×(j+1)]→L[ℝ] F)) (Fₗ:= (E →L[ℝ] (E [×j]→L[ℝ] F))) M (h.integ (j+1) p)).symm
lemma identity (j : ℕ) : iteratedFDeriv ℝ j (fun x=> ∫ i, f i x ∂μ) = fun x=> ∫ i, iteratedFDeriv ℝ j (f i) x ∂μ := by
   induction j with
   | zero =>
      simp_rw [iteratedFDeriv_zero_eq_comp, comp_apply]
      funext x
      exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
   | succ j IH =>
      funext x; rw [iteratedFDeriv_succ_eq_comp_left, comp_apply, IH, (h.grad x j).fderiv]; exact LinearIsometryEquiv.symm_apply_apply ..
lemma contDiff : ContDiff ℝ ∞ (fun x=>∫ i, f i x ∂μ) := by
   apply contDiff_of_differentiable_iteratedFDeriv
   intro j hj; rw [h.identity]; exact fun x=> (h.grad x j).differentiableAt
end Majorant

lemma affine_iterated (f : E → G) (h : ContDiff ℝ ∞ f) (A : F →L[ℝ] E) (y : E) (x : F) (j : ℕ) :
    iteratedFDeriv ℝ j (fun p : F => f (y + A p)) x = (iteratedFDeriv ℝ j f (y+A x)).compContinuousLinearMap fun _ => A := by
   change iteratedFDeriv ℝ j ((fun q : E => f (y+q)) ∘ A) x = _
   rw [A.iteratedFDeriv_comp_right (show ContDiff ℝ ∞ (fun q : E => f (y+q)) from by fun_prop) x (by exact_mod_cast le_top), iteratedFDeriv_comp_add_left]

lemma extDer {f : G×E → F} (h : ContDiff ℝ ∞ f) (x : E) (i : G) (j : ℕ) :
  iteratedFDeriv ℝ j (fun q : E => f (i,q)) x = (iteratedFDeriv ℝ j f (i,x)).compContinuousLinearMap fun _ => ContinuousLinearMap.inr ℝ G E := by
   simpa using affine_iterated f h (ContinuousLinearMap.inr ℝ G E) (i,0) x j

end YM.MS
