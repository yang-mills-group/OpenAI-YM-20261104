import YM.Integration.ActualOriginalQCharges
import YM.Integration.ActualRunKernelPackets

/-! The invariant real atom of an original registered color word sums all of its true
Haar-projected color components. Its paths are the actual transported curvature columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureAtom
open Function Finset Lattice Wilson RG MeasureTheory
open PhysicalNext.Repeat.Legato Source Labels
open NativeCurvatureTensor
open scoped Classical BigOperators

variable {G : Gauge} {k : ℕ}
variable (c : Fin k → G.ColorIndex) (q : Fin k → RG.Slot)

theorem real (j : Fin k → G.ColorIndex) :
    ((NativeCurvatureTensor.coefficient c j).re : ℂ) = NativeCurvatureTensor.coefficient c j := by
  let f (g : G.El) : ℝ := ∏ i, G.adjoint g (EuclideanSpace.basisFun _ ℝ (j i)) (c i)
  have h : NativeCurvatureTensor.coefficient c j = ((∫ g, f g ∂G.probHaar : ℝ) : ℂ) := by
    calc
      _ = ∫ g, ((f g : ℝ) : ℂ) ∂G.probHaar := by
        apply integral_congr_ae
        filter_upwards with g
        simp [f]
      _ = _ := integral_ofReal
  rw [h]
  rfl

def atom : Atom G k := ⟨q, fun j => (NativeCurvatureTensor.coefficient c j).re⟩

theorem read (x : Fin k → G.Color) :
    (((atom c q).poly x : ℝ) : ℂ) = value c x := by
  unfold atom Atom.poly value
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, real]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem invariant : (atom c q).Invariant := by
  intro u x
  apply Complex.ofReal_injective
  rw [read, read, value_invariant]

theorem magnitude :
    (atom c q).magnitude = ∑ j : Fin k → G.ColorIndex, ‖coefficient c j‖ := by
  unfold Atom.magnitude atom
  apply Finset.sum_congr rfl
  intro j _
  rw [← real c j, Complex.norm_real, Real.norm_eq_abs]

variable {n : Side}
theorem unmasked (o : Site n) (U : Config G n) :
    (((atom c q).unmasked U o : ℝ) : ℂ) = value c (fun i => (q i).atSite U o) :=
  read c q _

end YM.Integration.WilsonOriginalProjectedCurvatureAtom
