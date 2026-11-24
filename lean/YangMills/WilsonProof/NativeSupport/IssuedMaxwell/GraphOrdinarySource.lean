import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphCoefficients
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphOrdinary
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphCoefficients
open YM YangMills.MSbar IssuedMaxwell.Reports
open Set Filter
variable (g:YangMills.GaugeGroup)

theorem source (simple:g.IsSimple): (issued g).correlation=GraphCorrelation.read g ∧
    (issued g).ope=Ordinary.read (B g) (GraphOrdinary.original g simple):=
  ⟨rfl,(GraphOrdinary.numerical g simple).symm⟩
end IssuedMaxwell.GraphCoefficients
end
