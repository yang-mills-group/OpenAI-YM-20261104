import YM.Integration.WilsonMeasuredPublicEntranceCoverCells
/-! Passage to the cutoff and period limits of a fixed smooth reporting stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceSmoothWeights
open Function Filter Set MeasureTheory Lattice Extraction
open WilsonMeasuredPublicEntranceCoverCells
open scoped Classical BigOperators Topology
variable {α:Type}{n:ℕ}{l:Filter α}(φ:Test n)(a r:ℝ)(pos:0<a)

include pos in
theorem limit (D:α→(Fin n→ Cover)→ℂ)(T:(Fin n→ Cover)→ℂ)
    (atCell:∀o,mass φ a r o≠0→Tendsto (fun z=>D z o) l (𝓝 (T o))):
    Tendsto (fun z=>φ.applyTo (fun x=>D z (address a (r • x)))) l (𝓝 (φ.applyTo (fun x=>T (address a (r • x))))) :=by
  classical
  obtain ⟨nodes,room⟩:=finite φ a r pos
  simp_rw [tested φ a r pos nodes room]
  apply tendsto_finsetSum
  intro o _
  by_cases empty:mass φ a r o=0
  · simp only [empty,zero_mul];exact tendsto_const_nhds
  · exact (atCell o empty).const_mul _

include pos in
theorem sub (D T:α→(Fin n→ Cover)→ℂ)(z:α):
    φ.applyTo (fun x=>D z (address a (r • x)))-φ.applyTo (fun x=>T z (address a (r • x)))=
      φ.applyTo (fun x=>(D z (address a (r • x))-T z (address a (r • x)))):=by
  obtain ⟨nodes,room⟩:=finite φ a r pos
  rw [tested φ a r pos nodes room, tested φ a r pos nodes room, tested φ a r pos nodes room (fun o=>D z o-T z o)]
  simp only [mul_sub,Finset.sum_sub_distrib]

end YM.Integration.WilsonMeasuredPublicEntranceSmoothWeights
end
