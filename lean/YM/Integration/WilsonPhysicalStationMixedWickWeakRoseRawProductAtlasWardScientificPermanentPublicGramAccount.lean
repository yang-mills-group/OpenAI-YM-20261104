import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicSparseFrame

noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicGramAccount
open Filter Function Matrix
open scoped Topology BigOperators Matrix Classical
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true

variable {I:Type*}[Fintype I][DecidableEq I]
theorem recover (M:Matrix I I ℂ)(paid:IsUnit M.det)(v:I→ℂ):
    M⁻¹ *ᵥ (M *ᵥ v)=v:=by
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ paid,Matrix.one_mulVec]

theorem original (A:Matrix I I ℂ)(c:I→ℂ)(Ak:ℕ→Matrix I I ℂ)(b E:ℕ→I→ℂ)
    (dual:IsUnit A.det)(gram:Tendsto Ak atTop (𝓝 A))
    (marked:Tendsto b atTop (𝓝 (A *ᵥ c)))(read:∀ᶠ k in atTop,Ak k *ᵥ E k=b k):
    Tendsto E atTop (𝓝 c) ∧ ∃C:ℝ,0<C ∧ ∀ᶠ k in atTop,(∑i,‖E k i‖)≤C:=by
  have nonzero:A.det≠0:=isUnit_iff_ne_zero.mp dual
  have dets:=((continuous_id.matrix_det).continuousAt (x:=A)).tendsto.comp gram
  have mature:=dets.eventually_ne nonzero
  have inverse:ContinuousAt Inv.inv A:=
    continuousAt_matrix_inv A (by rw [Ring.inverse_eq_inv'];exact continuousAt_inv₀ nonzero)
  have inverses:Tendsto (fun k=>(Ak k)⁻¹) atTop (𝓝 A⁻¹):=inverse.tendsto.comp gram
  have rhs:Tendsto (fun k=>(Ak k)⁻¹ *ᵥ b k) atTop (𝓝 (A⁻¹ *ᵥ (A *ᵥ c))):=by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_finsetSum _ (fun j _=>((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp inverses i) j).mul
      (tendsto_pi_nhds.mp marked j)))
  rw [recover A dual c] at rhs
  have limit:Tendsto E atTop (𝓝 c):=by
    apply rhs.congr'
    filter_upwards [mature,read] with k allowed bill
    rw [← bill,recover (Ak k) (isUnit_iff_ne_zero.mpr allowed)]
  have salaries:Tendsto (fun k=>∑i,‖E k i‖) atTop (𝓝 (∑i,‖c i‖)):=
    tendsto_finsetSum _ (fun i _=>(tendsto_pi_nhds.mp limit i).norm)
  refine ⟨limit,(∑i,‖c i‖)+1,by positivity,?_⟩
  exact (salaries.eventually (gt_mem_nhds (lt_add_one _))).mono fun k h=>le_of_lt h

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicGramAccount
end
