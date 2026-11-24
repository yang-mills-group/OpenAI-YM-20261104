import YM.Comparison.RG02.Bulk.Sequence
import YM.UVExtension.Oasis.Flora
/-! Chain attaches to the SAME UV family. Needs Floral (or supply explicitly), not Makes alone. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Bulk.Chain
open Function Filter Precision RG RG.Supply Wilson Lattice Exterior Tree
open Marker
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {hG : G.Simple} {C : Family G} (H : UVExtension.Oasis.Floral C (hG:=hG))
include H
theorem at_Oasis : Nonempty (Chain C.path) := by
   obtain ⟨M,T,A,R,S,U,t,K,w,Q,L,-,rfl,hO,-⟩:=H
   refine ⟨M.p,T,A.post,A.B.M,M.O,M.oga,A.B.kin,A.B.support,?_,?_⟩
   · exact fun N p m hp=> (hO.actual m p N hp 0 (by rw [abs_zero]; exact hO.open_at)).1
   exact fun N p m hp=> (hO.actual m p N hp 0 (by rw [abs_zero]; exact hO.open_at)).2.1
end YM.Comparison.RG02.Bulk.Chain
