import YM.Integration.WilsonOriginalFiledBochner

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledWeight
open Set Filter Lattice Wilson RG MeasureTheory Finset
open scoped Topology Classical BigOperators
variable {G:Gauge}{c f:Side}(S:StepData c f)(branches:S.patch.Branches S.kernel G)
  (β:ℝ)(V:Config G c)

include branches

/-- The reciprocal at a single original coarse configuration is bounded on its actual Haar source. -/
theorem minorant:∃z:ℝ,0<z ∧ ∀U:Config G f,z≤S.density β U V:=by
  let spring:=fun Q:Config G c × Config G c=>S.noise β Q.1 Q.2
  have cont:Continuous spring:=S.noise_cont β
  obtain ⟨Q,_,least⟩:=isCompact_univ.exists_isMinOn Set.univ_nonempty cont.continuousOn
  have weight (b:Edge (Site c)):0<(S.penaltyZ β G)⁻¹*S.penaltyWeight β (Q.2 b * (Q.1 b)⁻¹):=
    mul_pos (inv_pos.mpr (S.penaltyZ_pos β)) (Real.exp_pos _)
  have positive:0<spring Q:=Finset.prod_pos fun b _=>weight b
  have bottom (x:Config G c × Config G c):spring Q ≤ spring x:=@least x (Set.mem_univ x)
  refine ⟨spring Q,positive,fun U=>?_⟩
  calc
    spring Q=(∑t,S.likelihood U t)*(spring Q):=by rw [S.chosen branches U,one_mul]
    _≤S.density β U V:=by
      rw [Finset.sum_mul,StepData.density]
      exact Finset.sum_le_sum fun t _=>mul_le_mul_of_nonneg_left (bottom (S.prediction U t,V))
        (S.likelihood_pos U t)

/-- A nonzero issued whole-vector integral certifies absolute Bochner intake. -/
theorem received {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
    (F:Config G f→E)(survives:S.push β F V ≠ 0):Integrable F (prior G f):=by
  have paid:Integrable (fun U=>S.density β U V • F U) (prior G _):=by
    by_contra h
    exact survives (integral_undef h)
  obtain ⟨z,pos,lower⟩:=minorant S branches β V
  have measurable:Measurable (fun U:Config G f=>(S.density β U V)⁻¹):=
    ((S.density_meas branches β).comp (measurable_id.prodMk measurable_const)).inv
  have purchase:=paid.bdd_smul z⁻¹ measurable.aestronglyMeasurable (ae_of_all _ (fun U=>
    show ‖(S.density β U V)⁻¹‖≤z⁻¹ by
      rw [Real.norm_of_nonneg (inv_nonneg.mpr (pos.le.trans (lower U)))]
      exact inv_anti₀ pos (lower U)))
  apply purchase.congr
  exact ae_of_all _ fun U=>by
    change (S.density β U V)⁻¹ • (S.density β U V • F U)=F U
    rw [smul_smul,inv_mul_cancel₀ ((pos.trans_le (lower U)).ne'),one_smul]

end YM.Integration.WilsonOriginalFiledWeight
end
