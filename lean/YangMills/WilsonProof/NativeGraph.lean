import YangMills.PerturbativeMatching.Reference
import YangMills.WilsonProof.GraphOperands

set_option autoImplicit false
noncomputable section

namespace YM.MS.Graphical

open scoped BigOperators Classical

/-- Expand each external field in the basis of the common finite sector. For
each basis tuple the continuum evaluator sums the renormalized graphs of order
k at the insertion positions. The multilinear coordinate form weights that
value by the coefficients of the external fields. -/
def correlationForm {n : ℕ} (G : Gauge) (grade : ℕ) (x : Points n) (k : ℕ) :
    YM.XSpace.Structure1.Point G grade n :=
  let BasisIndex := YM.FVA2.Dframe.Toon G grade
  let vertexPolynomials := YM.FVA2.Position.OpenAxis.Plot (YM.FVA2.Press.portDeck G)
  let positions := YM.FVA2.Arrival.Schedule.plot x
  ∑ basisTuple : Fin n → BasisIndex,
    let insertions := YM.FVA2.Dframe.flash ∘ basisTuple
    let coordinateProduct := YM.FVA2.Dframe.each basisTuple
    fullGraph vertexPolynomials insertions (YM.FVA2.Teller.logNu 1)
      positions Finset.univ k • coordinateProduct

end YM.MS.Graphical

namespace YangMills.CorrelationMatching

open scoped BigOperators Classical

/-- The numerical coefficient of order k, with all external fields included
in the smallest common sector. The graph sum uses unit reference scale. -/
def graphCoefficient (g : GaugeGroup) :
    (n k : ℕ) → (Fin n → Σ d, (maxwellReference g).sector d) → Points n → ℂ :=
  fun _ k fields x =>
    let grade := Finset.univ.sup (fun i => (fields i).1)
    YM.MS.Graphical.correlationForm g.core grade x k (fun i =>
      YM.XSpace.Normalize.up
        (Finset.le_sup (f := fun j => (fields j).1) (Finset.mem_univ i)) (fields i).2)

end YangMills.CorrelationMatching

namespace YangMills.WilsonProof
open PerturbativeMatching

/-- Both evaluators expand the same basis tuple and insert its coordinates
at the same positions and logarithmic scale. -/
theorem sameGraphForm {n : ℕ} (G : YM.Gauge) (grade : ℕ) (x : YM.Points n) (k : ℕ) :
    YM.MS.Graphical.msbarCorrelationForm G grade x k =
      YM.MS.Graphical.correlationForm G grade x k := rfl

theorem sameGraphArray (g : GaugeGroup) :
    graphCorrelation g = CorrelationMatching.graphCoefficient g := rfl

theorem graphDetermined {g : GaugeGroup}
    (issued : MSbar.Ordinary.Determined (maxwellReference g) (CorrelationMatching.graphCoefficient g)) :
    OPEIsDetermined g := by
  unfold OPEIsDetermined
  rwa [sameGraphArray]

theorem graphOPE {g : GaugeGroup} (d : OPEIsDetermined g)
    (O : MSbar.Ordinary.OPE (maxwellReference g))
    (valid : MSbar.Ordinary.Valid (maxwellReference g) (CorrelationMatching.graphCoefficient g) O) :
    O = (msbarCoefficients g d).ope := by
  apply (valid_iff_eq_reference g d O).mp
  rwa [sameGraphArray]

end YangMills.WilsonProof
