import YangMills.WilsonProof.NativeGraph
import FormalConversion
import MSReference
import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields
import YangMills.WilsonProof.NativeSupport.MaxwellBridge
import YM.FVA2.Dframe.Trace
import YM.FVA2.Teller.Mass
import YM.XSpace.Grades
import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.Panels

set_option autoImplicit false
noncomputable section

namespace YM.MS.Graphical

open scoped BigOperators Classical


end YM.MS.Graphical

namespace YangMills.CorrelationMatching

open Matching
open scoped BigOperators Classical


/-- The degree-k coefficient after substituting the formal coupling change and
the field change on each insertion. All sums are finite at a fixed order. -/
def convertedCoefficient (g : GaugeGroup) (S : Conversion (maxwellReference g))
    {n : ℕ} (k : ℕ) (fields : Fin n → Label (maxwellReference g)) (x : Points n) : ℂ :=
  ∑ degrees : Fin n → Fin (k + 1), ∑ j : Fin (k + 1),
    let used := ∑ i, (degrees i).val
    if used ≤ k then
      (couplingPower S.f j.val (k - used) : ℂ) *
        graphCoefficient g n j.val (S.inputs fields degrees) x
    else 0

end YangMills.CorrelationMatching
