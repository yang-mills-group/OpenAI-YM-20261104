import YangMills.WilsonProof.PublicView
import YangMills.WilsonProof.NativeSupport.YangMills.Wightman
import YM.Fields.System

/-! The public Hilbert space, domain, labels, fields and affine action are the
ones of the supplied reconstruction. There is no second field-system witness. -/
set_option autoImplicit false
noncomputable section
namespace YangMills
open MeasureTheory Set Function
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius
variable {G : YM.Gauge} {L : YM.Register G} {S : YM.Table L}
variable (A : YM.Boundary.Wightman S)








end YangMills
