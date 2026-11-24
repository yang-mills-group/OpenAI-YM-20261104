import YM.Integration.WilsonOriginalCartesianJetComponents

/-! Read every genuine separated jet on an affine chart, locally in its original domain. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAffineShapeJets
open Set Filter
open scoped ContDiff Topology
variable {E G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem original (j : ℕ) (f : E → F) {O : Set E} (opn : IsOpen O)
    (s : ContDiffOn ℝ j f O) (a : E) (L : G →L[ℝ] E) {x : G} (hx : a+L x ∈ O) :
    iteratedFDeriv ℝ j (fun z => f (a+L z)) x =
      (iteratedFDeriv ℝ j f (a+L x)).compContinuousLinearMap (fun _ => L) := by
  let P := (fun v : E => a+v) ⁻¹' O
  have op : IsOpen P := opn.preimage (continuous_const.add continuous_id)
  have pre : IsOpen (L ⁻¹' P) := op.preimage L.continuous
  have sf : ContDiffOn ℝ j (fun v => f (a+v)) P :=
    s.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hy => hy)
  have q := L.iteratedFDerivWithin_comp_right sf op.uniqueDiffOn pre.uniqueDiffOn
    (show L x ∈ P from hx) (i := j) (le_refl _)
  rw [iteratedFDerivWithin_of_isOpen j pre (show x ∈ L ⁻¹' P from hx),
      iteratedFDerivWithin_of_isOpen j op (show L x ∈ P from hx)] at q
  simpa only [Function.comp_def,iteratedFDeriv_comp_add_left] using q

end YM.Integration.WilsonOriginalAffineShapeJets
