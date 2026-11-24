import YangMills.WilsonProof.NativeSupport.IssuedRuns.FinalWilsonData
import YM.Nonperturbative.HeadlineSpec

set_option autoImplicit false

namespace IssuedRuns.FinalWilsonData

open YangMills YangMills.Wilson Filter
open scoped Topology
noncomputable section

variable {g : GaugeGroup}

abbrev latticeData (C : YM.Family g.core) (qualified : C.Makes)
    (hg : g.IsSimple) (B : Maxwell.Reference g) : WilsonData B (wilsonFamily C) :=
  IssuedRuns.FinalWilsonData.original C qualified hg B

#print axioms latticeData

end
end IssuedRuns.FinalWilsonData
