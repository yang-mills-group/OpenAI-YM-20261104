import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Algebra.BigOperators.Pi

/-! Expand only the selected physical slots of the original multilinear map.
All other arguments, including coupling and Gaussian directions, stay fixed. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FixedArgumentMultilinear

open scoped BigOperators

/-- Exact finite expansion with arbitrary fixed nonphysical arguments.
Any original scalar normalization remains inside T. -/
theorem expand_physical_slots
    {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {n : ℕ} {R P I : Type*} [Fintype P] [DecidableEq P] [Fintype I]
    (e : Fin n ≃ R ⊕ P)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) Z)
    (x : R → E) (ψ : I → E) (w : I → ℝ) :
    T (fun k => Sum.elim x (fun _p => ∑ i : I, w i • ψ i) (e k)) =
      ∑ y : P → I, (∏ p : P, w (y p)) •
        T (fun k => Sum.elim x (fun p => ψ (y p)) (e k)) := by
  let M : MultilinearMap ℝ (fun _ : P => E) Z :=
    (T.toMultilinearMap.domDomCongr e).currySum x
  change M (fun _p => ∑ i : I, w i • ψ i) = _
  calc
    _ = ∑ y : P → I, M (fun p => w (y p) • ψ (y p)) :=
      M.map_sum (fun _p i => w i • ψ i)
    _ = ∑ y : P → I, (∏ p : P, w (y p)) • M (fun p => ψ (y p)) := by
      apply Finset.sum_congr rfl
      intro y _hy
      exact M.map_smul_univ (fun p => w (y p)) (fun p => ψ (y p))
    _ = _ := rfl

end YM.Integration.FixedArgumentMultilinear
end
