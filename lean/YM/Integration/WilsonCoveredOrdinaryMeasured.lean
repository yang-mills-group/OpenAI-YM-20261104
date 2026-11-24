import YM.Integration.WilsonCoveredOrdinaryPolynomial
import YM.Integration.WilsonThermometerRegisteredTrace

/-! On a fixed issued bank, taking the total coupling degree of each ordinary face preserves
continuity in the actual angle. This licenses evaluation at a measurable local gauge. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoveredOrdinaryMeasured
open Finset RG Lattice Wilson Exterior Next.SectorChange Multi Marker Comparison.RG02
open QuadraticLocal Earn WilsonCoveredOrdinaryPolynomial WilsonIndependentOrdinaryPairGrade
open scoped Topology BigOperators Classical

private theorem product {X I : Type*} [TopologicalSpace X] (t : Finset I)
    (f : I → X → Polynomial ℂ) (hc : ∀ i d, Continuous (fun x => (f i x).coeff d)) :
    ∀ d, Continuous (fun x => (∏ i∈t,f i x).coeff d) := by
  induction t using Finset.induction_on with
  | empty => intro d; simp only [Finset.prod_empty]; exact continuous_const
  | insert i t miss ih =>
    intro d
    simp only [Finset.prod_insert miss,Polynomial.coeff_mul]
    exact continuous_finsetSum _ (fun ij _ => (hc i ij.1).mul (ih ij.2))

theorem original {V : Type} [Fintype V] [DecidableEq V] {R : Census V} {G : Gauge} {n : Side}
    (M : Bulk.Colors R G n) (order : ℕ) (g : ℂ) (s : R.Mode) :
    Continuous (fun x : fieldDir G n 1 =>
      evaluated order (fun d=>Air.discharge M d x) g s) := by
  unfold evaluated partialValue
  apply continuous_finsetSum
  intro d _
  apply continuous_const.mul
  simp only [ordinary,Polynomial.finsetSum_coeff]
  apply continuous_finsetSum
  intro h _
  apply product h.val
  intro v e
  simp only [coefficient]
  split
  · exact WilsonThermometerRegisteredTrace.coefficient M e v.val
  · exact continuous_const

end YM.Integration.WilsonCoveredOrdinaryMeasured
