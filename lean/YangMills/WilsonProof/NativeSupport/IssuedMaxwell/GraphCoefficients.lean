import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphCorrelation
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphReader
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphCoefficients
open YM YangMills.MSbar IssuedMaxwell.Reports
open Set Filter
variable (g:YangMills.GaugeGroup)

def issued:Coefficients (B g):=⟨GraphCorrelation.read g,GraphReader.name g⟩

end IssuedMaxwell.GraphCoefficients
end
