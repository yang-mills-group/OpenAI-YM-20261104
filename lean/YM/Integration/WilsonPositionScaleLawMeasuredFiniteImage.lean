import YM.Integration.WilsonPositionScaleLawMeasuredBorel
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredFiniteImage
open Filter Finset
open scoped Topology BigOperators Classical
variable {V E I:Type*}[AddCommGroup V][Module ℂ V]
    [NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E]

theorem original (survey:V→ₗ[ℂ]E)(debt:I→V→ₗ[ℂ]ℂ)(u:Filter I)(s:I→ℝ)
    (positive:∀ᶠa in u,0 ≤ s a)(passes:∀a v,survey v=0→debt a v=0)
    (test:∀v:V,∃K:ℝ,0≤K ∧ ∀ᶠa in u,‖debt a v‖≤K*s a) :
    ∃K:ℝ,0≤K ∧ ∀ᶠa in u,∀v:V,‖debt a v‖≤(K*‖survey v‖)*s a:=by
  let B:=Module.finBasis ℂ (LinearMap.range survey)
  let L:(LinearMap.range survey)→L[ℂ](Fin (Module.finrank ℂ (LinearMap.range survey))→ℂ):=
    B.equivFun.toLinearMap.toContinuousLinearMap
  choose submitted invoice using fun i=>(B i).property
  choose k hk hp using fun i=>test (submitted i)
  refine ⟨‖L‖*(∑i,k i),mul_nonneg L.opNorm_nonneg (sum_nonneg fun i _=>hk i),?_⟩
  filter_upwards [eventually_all.mpr hp,positive] with a bank pos v
  let w:LinearMap.range survey:=⟨survey v,⟨v,rfl⟩⟩
  have column (i):‖L w i‖≤‖L‖*‖survey v‖:=
    (norm_le_pi_norm (L w) i).trans (L.le_opNorm w)
  have restore:(∑i,(L w i) • survey (submitted i))=survey v:=by
    simp_rw [invoice]
    have sum:(LinearMap.range survey).subtype (∑i,L w i • B i)=(LinearMap.range survey).subtype w :=
      congrArg (LinearMap.range survey).subtype (B.sum_repr w)
    simpa only [map_sum,map_smul,Submodule.subtype_apply] using sum
  have zeros:survey (v-∑i,(L w i) • submitted i)=0:=by
    rw [map_sub,map_sum];simp_rw [map_smul];rw [restore,sub_self]
  have e:=passes a _ zeros
  rw [map_sub,sub_eq_zero,map_sum] at e
  simp_rw [map_smul] at e
  rw [e]
  calc
    _≤∑i,‖(L w i) • (debt a (submitted i))‖:=norm_sum_le _ _
    _≤∑i,(‖L‖*‖survey v‖)*(k i*s a):=by
      apply sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (column i) (bank i) (norm_nonneg _) (mul_nonneg L.opNorm_nonneg (norm_nonneg _))
    _=_:=by rw [←mul_sum,←sum_mul];ring
end YM.Integration.WilsonPositionScaleLawMeasuredFiniteImage
