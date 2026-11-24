import YM.FormalOPE.RG10.Profile.Relax
/-! Slice derivative continuity in the anchored test topology; work on product space. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Profile
open Function MeasureTheory Filter Topology Metric TopologicalSpace Set ContDiffMapSupportedIn
open scoped Topology Distributions ContDiff Classical BoundedContinuousFunction
variable {E W F : Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
    [NormedAddCommGroup W][NormedSpace ℝ W][NormedAddCommGroup F][NormedSpace ℝ F]
    {K:Compacts E} (L: W → 𝓓_{K}(E,F))(h: ContDiff ℝ ∞ (fun p:W×E=>L p.1 p.2))
-- regularity of the entire remaining-coordinate derivative
include h
lemma sheet (m:ℕ) : ContDiff ℝ ∞ (fun p:W×E=>iteratedFDeriv ℝ m (L p.1) p.2) := by
 induction m with
 | zero=> exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.contDiff).comp h
 | succ m h=>
   rw [show (fun p:W×E=>iteratedFDeriv ℝ (m+1) (L p.1) p.2) = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1)=>E) F).symm ∘ (fun p:W × E=> fderiv ℝ (iteratedFDeriv ℝ m (L p.1)) p.2) from rfl]
   refine ContDiff.comp (f:=fun p:W × E=> fderiv ℝ (iteratedFDeriv ℝ m (L p.1)) p.2) ?_ ?_
   · let T := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1)=>E) F).symm.toContinuousLinearEquiv; exact ContinuousLinearEquiv.contDiff (E:=E →L[ℝ] E [×m]→L[ℝ] F) (F:=E [×(m+1)]→L[ℝ] F) (𝕜:=ℝ) T
   apply ContDiff.fderiv (f:=fun p: W×E=> iteratedFDeriv ℝ m (L p.1)) (n:=∞) _ contDiff_snd (hnm:=show _ ≤ ∞ from by simp)
   exact h.comp (f:=fun x:(W×E)×E=>(x.1.1,x.2)) (by fun_prop)

variable [ProperSpace W]
theorem volumeContinuous : Continuous L := by
 apply (continuous_iff_comp _).mpr; intro i
 refine continuous_iff_continuousAt.mpr fun x=> BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr ?_
 simp_rw [Function.comp_apply,structureMapCLM_top_apply]
 apply Metric.tendstoUniformly_iff.mpr; intro ε hε
 obtain ⟨δ,hδ,hh⟩:= Metric.uniformContinuousOn_iff.mp (((isCompact_closedBall x 1).prod K.isCompact).uniformContinuousOn_of_continuous (sheet L h i).continuous.continuousOn) ε hε
 filter_upwards [ball_mem_nhds x hδ,closedBall_mem_nhds x (show (0:ℝ)<1 from zero_lt_one)] with y hy hv a
 by_cases ha:a ∈ K
 · apply hh (x:=(x,a)) (y:=(y,a)) (Set.mk_mem_prod (by simp) ha) ⟨hv,ha⟩; simpa [Prod.dist_eq, dist_comm x y] using (show dist y x <δ from hy)
 rw [(L _).iteratedFDeriv_zero_on_compl ha,(L _).iteratedFDeriv_zero_on_compl ha,dist_self]; exact hε
end YM.FormalOPE.RG10.Profile
