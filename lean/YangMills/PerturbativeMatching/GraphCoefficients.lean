import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import YangMills.MaxwellReference
import YM.FVA2.Position.Table
import YM.FVA2.Press.Deck
import YM.MS.Theater.Horizon
import YM.MS.Graphical.Panels

set_option autoImplicit false
noncomputable section

namespace YM.MS.Graphical

open scoped BigOperators Classical

/-- Expand each external field in the basis of the common finite sector. For
each basis tuple the continuum evaluator sums the renormalized graphs of order
k at the insertion positions. The multilinear coordinate form weights that
value by the coefficients of the external fields. -/
def msbarCorrelationForm {n : ℕ} (G : Gauge) (grade : ℕ) (x : Points n) (k : ℕ) :
    MultilinearMap ℂ (fun _ : Fin n => YM.Maxwell.shellSector G grade) ℂ :=
  let gradedBasis := YM.FVA2.Press.portDeck G
  let BasisIndex := YM.MS.Menus.Glyph gradedBasis grade
  let vertexPolynomials := YM.FVA2.Position.OpenAxis.Plot gradedBasis
  let positions := fun i => YM.MS.Theater.out (x i)
  let msbarLogScale := Real.log 1 + (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2
  let insertionLabel (i : BasisIndex) : YM.MS.Rake.Label gradedBasis := ⟨i.1.val, ⟨i.2.1, i.2.2⟩⟩
  let coordinates := YM.MS.Theater.Daylight gradedBasis grade
  ∑ basisTuple : Fin n → BasisIndex,
    let insertions := insertionLabel ∘ basisTuple
    let coordinateProduct := (MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap
       (fun i => coordinates.coord (basisTuple i))
    fullGraph vertexPolynomials insertions msbarLogScale
      positions Finset.univ k • coordinateProduct

end YM.MS.Graphical

namespace YangMills.PerturbativeMatching

open scoped BigOperators Classical

/-- The numerical coefficient of order k, with all external fields included
in the smallest common sector. The graph sum uses unit reference scale. -/
def graphCorrelation (g : GaugeGroup) :
    (n k : ℕ) → (Fin n → Σ d, (maxwellReference g).sector d) → Points n → ℂ :=
  fun _ k fields x =>
    let grade := Finset.univ.sup (fun i => (fields i).1)
    YM.MS.Graphical.msbarCorrelationForm g.core grade x k (fun i =>
      Submodule.inclusion (YM.Maxwell.Free.chain
        (Finset.le_sup (f := fun j => (fields j).1) (Finset.mem_univ i))) (fields i).2)

end YangMills.PerturbativeMatching
