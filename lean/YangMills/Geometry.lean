import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Star.Unitary

/-! Compact matrix gauge groups and separated configurations in four dimensions. -/
set_option autoImplicit false
noncomputable section
namespace YangMills
open MeasureTheory Set Function TopologicalSpace
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius

/-! ## Compact simple matrix gauge groups -/

/-- The fixed faithful unitary representation used to describe a gauge
group. -/
abbrev UnitaryRepresentation (n : ℕ) := Matrix.unitaryGroup (Fin (n + 1)) ℂ

/-- A compact matrix gauge group together with its one-parameter Lie
algebra.  The last field prevents the Lie algebra from being arbitrary: it
consists exactly of the matrices whose exponentials stay in the group. -/
structure GaugeGroup where
  n : ℕ
  image : Subgroup (UnitaryRepresentation n)
  imageClosed : IsClosed (image : Set (UnitaryRepresentation n))
  lieAlgebra : Submodule ℝ (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  generates : ∀ X,
    X ∈ lieAlgebra ↔
      ∀ t : ℝ, NormedSpace.exp (t • X) ∈
        Set.range (fun u : image ↦ (u.1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))

namespace GaugeGroup

/-- Real simplicity of the Lie algebra, including the nonabelian
condition. -/
def IsSimple (gauge : GaugeGroup) : Prop :=
  (∃ X ∈ gauge.lieAlgebra, ∃ Y ∈ gauge.lieAlgebra,
    X * Y - Y * X ≠ 0) ∧
  ∀ ideal : Submodule ℝ (Matrix (Fin (gauge.n + 1)) (Fin (gauge.n + 1)) ℂ),
    ideal ≤ gauge.lieAlgebra →
    (∀ X ∈ gauge.lieAlgebra, ∀ Y ∈ ideal, X * Y - Y * X ∈ ideal) →
    ideal = ⊥ ∨ ideal = gauge.lieAlgebra

end GaugeGroup

/-! ## Spacetime and test functions -/

abbrev Axis := Fin 4
abbrev SpaceAxis := Fin 3
abbrev timeAxis : Axis := Fin.last 3
abbrev Spacetime := EuclideanSpace ℝ Axis
abbrev Space := EuclideanSpace ℝ SpaceAxis

abbrev Points (n : ℕ) := PiLp 2 (fun _ : Fin n => Spacetime)

def separated (n : ℕ) : Opens (Points n) :=
  ⟨{x | Function.Injective x.ofLp}, by
    classical
    have eqSet : {x : Points n | Function.Injective x.ofLp} =
        ⋂ (i : Fin n) (j : Fin n) (_ : i ≠ j), {x : Points n | x i ≠ x j} := by
      ext x
      simp only [mem_setOf_eq, mem_iInter]
      exact ⟨fun h i j hij => fun he => hij (h he), fun h i j he => by_contra fun hij => h i j hij he⟩
    rw [eqSet]
    apply isOpen_iInter_of_finite; intro i
    apply isOpen_iInter_of_finite; intro j
    apply isOpen_iInter_of_finite; intro _
    exact isOpen_ne_fun (PiLp.continuous_apply _ _ i) (PiLp.continuous_apply _ _ j)⟩

abbrev SeparatedTest (n : ℕ) := _root_.TestFunction (separated n) ℂ ⊤

end YangMills
