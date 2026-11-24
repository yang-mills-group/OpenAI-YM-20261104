import YangMills.PhysicalOPE.SingleCluster
import YangMills.WilsonProof.NativeSupport.YangMills.CorrelationHierarchy

/-! Geometric error of the *same* physical OPE, in fixed physical fields.
The perturbative order is a separate truncation parameter. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.Hierarchy

open Filter Set
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)



end YangMills.Hierarchy
