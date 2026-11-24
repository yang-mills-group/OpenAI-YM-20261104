import YM.Integration.WilsonPositionProgramInvertedStencil

/-! The product over genuine independent sites is expanded on the same
off-tree inversion coordinates before the common Gaussian denominator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramInvertedWords
open Function Finset Filter Lattice XSpace PhysicalNext.Repeat.Legato Precision
open PertExtension.Orb WilsonPositionProgramInvertedStencil WilsonPositionProgramInversionMaterial
open scoped Classical BigOperators ContDiff Topology
variable {G : Gauge} {p : Period} (T : p.Tree) {I : Type} [Fintype I] [LinearOrder I]

omit [Fintype I] [LinearOrder I] in
theorem multiply (P : I → T.Field G → ℂ)
    (smooth : ∀ i,ContDiffAt ℝ ω (P i) 0) :
    ∀ S : Finset I, ContDiffAt ℝ ω (∏i∈S,P i) 0 ∧
      Taylor.expandTaylor (T.basis G) (∏i∈S,P i) =
        ∏i∈S,Taylor.expandTaylor (T.basis G) (P i) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    constructor
    · change ContDiffAt ℝ ω (fun _ : T.Field G => (1:ℂ)) 0
      exact contDiffAt_const
    · change Taylor.expandTaylor _ (fun _ : T.Field G => (1:ℂ))=1
      rw [Taylor.expand_const]
      simp
  | @insert i S fresh ih =>
    rw [Finset.prod_insert fresh,Finset.prod_insert fresh]
    exact ⟨(smooth i).mul ih.1,(Taylor.expand_mul (T.basis G) (smooth i) ih.1).trans
      (congrArg (Taylor.expandTaylor (T.basis G) (P i) * ·) ih.2)⟩

theorem original (R : Run G) (d : I → ℕ) (z : I → Cover) (a : Axes R d) :
    source R p d z T a =
      ∏ j, Taylor.expandTaylor (T.basis G) (Complex.ofRealCLM ∘
        (SlotEvaluation.fieldAt (R.family.localSection (d j)) (axis R d a j) (wrap p.side (z j)) ∘ T.links)) := by
  let P := fun j => Complex.ofRealCLM ∘
    (SlotEvaluation.fieldAt (R.family.localSection (d j)) (axis R d a j) (wrap p.side (z j)) ∘ T.links)
  have green j : ContDiffAt ℝ ω (P j) 0 := by
    let f := moved (p:=p) R (d j) (axis R d a j) (z j)
    have he : P j = Complex.ofRealCLM ∘ (f ∘ tangent T) := by
      apply congrArg (Complex.ofRealCLM ∘ ·)
      exact (funext (submitted T R (d j) (axis R d a j) (z j))).symm
    rw [he]
    have h : ContDiffAt ℝ ω f (tangent T (0:T.Field G)) := by
      rw [map_zero]
      exact curved R (d j) _ _
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (h.comp 0 (tangent T).contDiff.contDiffAt)
  have literal : Complex.ofRealCLM ∘ (WilsonPositionProgramCopyTop.planted R p d z (axis R d a) ∘ T.links) =
      ∏j,P j := by
    funext x
    change Complex.ofReal ((∏ j, SlotEvaluation.fieldAt (R.family.localSection (d j))
      (axis R d a j) (wrap p.side (z j))) (T.links x)) = _
    simp only [Finset.prod_apply,Complex.ofReal_prod,P,Function.comp_apply,Complex.ofRealCLM_apply]
  change Taylor.expandTaylor _ _ = ∏ j, Taylor.expandTaylor _ (P j)
  rw [literal]
  exact (multiply T P green univ).2

end YM.Integration.WilsonPositionProgramInvertedWords
end
