import MSGradeProjection
import FormalConversion
import MSReference
import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields

/-! Componentwise projections onto the engineering weights of gauge-invariant
curvature polynomials. A gauge rotation acts separately on each jet order, so
it commutes with the weighted dilation of a tower. Comparing coefficients of
the dilation parameter shows that each component remains gauge invariant. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section

namespace YangMills.Matching.Grade
open Set
open scoped BigOperators Classical

variable {g : GaugeGroup}









attribute [local irreducible] project diagonal




end YangMills.Matching.Grade
