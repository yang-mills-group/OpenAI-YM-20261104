import YM.Integration.WilsonOriginalAffineShapeJets

/-! Return a measured multilinear jet from an invertible physical chart.
The loss is the price of the same inverse on every occupied derivative. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalUnchartedTensor
open scoped Classical BigOperators
variable {E G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem original {j : ℕ} (L : G ≃L[ℝ] E) (A B : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) F) :
    ‖A-B‖ ≤ ‖A.compContinuousLinearMap (fun _ => L.toContinuousLinearMap) -
      B.compContinuousLinearMap (fun _ => L.toContinuousLinearMap)‖ * ‖L.symm.toContinuousLinearMap‖^j := by
  let C := A.compContinuousLinearMap (fun _ => L.toContinuousLinearMap) -
      B.compContinuousLinearMap (fun _ => L.toContinuousLinearMap)
  have back : C.compContinuousLinearMap (fun _ => L.symm.toContinuousLinearMap) = A-B := by
    ext u
    change A (fun k => L (L.symm (u k))) - B (fun k => L (L.symm (u k))) = A u-B u
    simp
  simpa only [back,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    C.norm_compContinuousLinearMap_le (fun _ => L.symm.toContinuousLinearMap)

end YM.Integration.WilsonOriginalUnchartedTensor
