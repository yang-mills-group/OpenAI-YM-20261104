import YM.Pert.Scale.MovingFunctional
noncomputable section
set_option autoImplicit false
namespace YM.Pert.Scale
open Function Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [ProperSpace E]

/-- Recover a desired free limit vector by inverting the changing evaluation matrices. -/
lemma control_inverse (L : ℕ→E ≃ₗ[ℂ] E) (L₀ : E ≃ₗ[ℂ] E) (a : ℕ→E) {a₀:E}
    (h : ∀ v, Tendsto (fun k=>L k v) atTop (𝓝 (L₀ v))) (ha : Tendsto a atTop (𝓝 a₀)) :
    Tendsto (fun k=> (L k).symm (a k)) atTop (𝓝 (L₀.symm a₀)) := by
  let B := Module.finBasis ℂ E
  have hc i : Continuous (B.coord i) := (LinearMap.toContinuousLinearMap (E:=E) (F':=ℂ) (B.coord i)).continuous
  let M k i := (B.coord i).comp (L k).toLinearMap
  let M' i := (B.coord i).comp L₀.toLinearMap
  let u k := (L k).symm (a k) - L₀.symm a₀
  suffices he : Tendsto u atTop (𝓝 0) from
     (zero_add (L₀.symm a₀)) ▸ (he.add (tendsto_const_nhds (f:=atTop) (x:=L₀.symm a₀))).congr (fun _=> sub_add_cancel ..)
  refine moving_zero (L:=M) (L₀:=M') (fun i v=>(hc i).continuousAt.tendsto.comp (h v)) ?_ (fun i=> ?_)
  · intro x hx
    by_contra! hp
    apply hx
    exact L₀.injective (by
       rw [map_zero]
       apply B.equivFun.injective; rw [map_zero]; exact funext hp)
  have he : Tendsto (fun k => a k - L k (L₀.symm a₀)) atTop (𝓝 0) :=
      by simpa only [LinearEquiv.apply_symm_apply,sub_self] using ha.sub (h (L₀.symm a₀))
  simp_rw[M,LinearMap.comp_apply,LinearEquiv.coe_coe,u,map_sub,LinearEquiv.apply_symm_apply]
  rw [← (B.coord i).map_zero]
  have ht := (hc i).continuousAt.tendsto.comp he
  exact ht.congr fun k => map_sub .. 

end YM.Pert.Scale
