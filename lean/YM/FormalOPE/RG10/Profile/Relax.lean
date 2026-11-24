import YM.Euclid.Test
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.Baire.CompleteMetrizable
/-!
# Completeness/Baire theorem used in taking WilsonX integrals
For the unit law we'll have to take a limit in the smooth-test topology on a *single*
compact in configuration space. Uniform convergence in amplitude alone isn't assumed to suffice.
Here derive the needed fact about test spaces rather than adding a premise.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Profile
open TopologicalSpace Set Function UniformSpace ContDiffMapSupportedIn Filter
open scoped BoundedContinuousFunction Topology Distributions ContDiff Classical
variable {E F : Type*}
    [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
    {K : Compacts E}
abbrev slide {K: Compacts E} := (ContinuousLinearMap.pi (structureMapCLM ℝ ⊤) : 𝓓_{K}(E,F) →L[ℝ] ∀ i:ℕ, E →ᵇ (E [×i]→L[ℝ] F))
local notation "chart" => slide (E:=E) (F:=F) (K:=K)

theorem slideClosed : Topology.IsClosedEmbedding (chart) := by
 refine ⟨(isUniformEmbedding_pi_structureMapCLM ℝ).isEmbedding, IsSeqClosed.isClosed ?_⟩
 intro v L hL hu
 choose y hy using hL
 have H i : TendstoUniformly (fun n:ℕ => iteratedFDeriv ℝ i (y n)) (L i) atTop := by
   simp_rw [← structureMapCLM_top_apply ℝ]; exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (by
     change Tendsto (fun n=> chart (y n) i) _ _; simp_rw [hy]; exact tendsto_pi_nhds.mp hu i)
 let cur (n:ℕ) := continuousMultilinearCurryLeftEquiv ℝ (fun _: Fin (n+1)=> E) F
 have hd : ∀ (n:ℕ) (x:E), HasFDerivAt (L n) (cur n (L (n+1) x)) x := by
   intro n x; let y' k := iteratedFDeriv ℝ n (y k)
   have he i : fderiv ℝ (y' i)= cur n ∘ iteratedFDeriv ℝ (n+1) (y i):= fderiv_iteratedFDeriv
   exact hasFDerivAt_of_tendstoUniformly (g':=(cur n) ∘ L (n+1)) (f:=y') (f':=fun i=>fderiv ℝ (y' i))
        (by simp_rw [he]; exact (cur n).isometry.uniformContinuous.comp_tendstoUniformly (H (n+1))) (fun i x=> ((y i).contDiff.differentiable_iteratedFDeriv (m:=n) (mod_cast ENat.coe_lt_top n) x).hasFDerivAt) (fun x=>(H n).tendsto_at x) x
 let g (x:E):=(L 0 x) 0
 have hs : ∀ n:ℕ, iteratedFDeriv ℝ n g = L n := by
   intro n; induction n with
   | zero=>ext x f; simp [iteratedFDeriv_zero_apply, g, Subsingleton.elim f 0]
   | succ n hn=> change (cur n).symm ∘ fderiv ℝ (iteratedFDeriv ℝ n g) = _; funext x; simp only [comp_apply, hn,(hd ..).fderiv, LinearIsometryEquiv.symm_apply_apply]
 let z : 𝓓_{K}(E, F) := ⟨g, contDiff_of_differentiable_iteratedFDeriv (fun n _ => by rw [hs]; exact fun x=> (hd n x).differentiableAt), fun x hx=> by
    have H' := (H 0).tendsto_at x; -- outside K
    have he : ∀ n:ℕ, iteratedFDeriv ℝ 0 (y n) x=0:=fun n=> (y n).iteratedFDeriv_zero_on_compl hx
    unfold g; rw [show L 0 x=0 from tendsto_nhds_unique H' (by simp_rw [he]; exact tendsto_const_nhds)]; rfl⟩
 exact ⟨z,funext fun i=> BoundedContinuousFunction.ext <| congr_fun (Eq.trans (structureMapCLM_top_apply ℝ z) (hs i))⟩

variable (E F K)[CompleteSpace F]
theorem relaxes : CompleteSpace 𝓓_{K}(E, F) := completeSpace_iff_isComplete_range (isUniformEmbedding_pi_structureMapCLM ℝ (F:=F)).isUniformInducing |>.2 (slideClosed.isClosed_range.isComplete)
theorem toll : BaireSpace 𝓓_{K}(E, F) := by
 haveI (i:ℕ) : IsCompletelyPseudoMetrizableSpace (E →ᵇ (E [×i]→L[ℝ] F)) := by infer_instance
 have hh:= slideClosed (E:=E) (F:=F) (K:=K) |>.IsCompletelyPseudoMetrizableSpace; infer_instance
end YM.FormalOPE.RG10.Profile
