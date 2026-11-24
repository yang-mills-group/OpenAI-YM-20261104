import YangMills.PhysicalOPE.FusionTree
import YangMills.PhysicalOPE.Tree
import YangMills.WilsonProof.NativeSupport.MatchingGeometry

/-! Finite nesting of the physical OPE. At every internal vertex we evaluate
the same physical coefficient function on its child centers. Summing a separate
physical channel at every non-root vertex gives the iterated truncation. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.Hierarchy

open Filter Set Function
open scoped Topology BigOperators Classical


namespace FusionTree
variable (t : FusionTree)






variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)







end FusionTree

variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)


end YangMills.Hierarchy
