import YM.Integration.WilsonOffsetJointRoster
import YangMills.WilsonProof.NativeSupport.FrozenComparison
import YM.RGComparison.Core16.Spool.Beacon
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Finset Lattice RG Wilson Labels Next.Foundations RGComparison.Core16 RGComparison.Core16.Spool PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
namespace WilsonReportFrozenTraversal
open WilsonConditionalTaylorLabels WilsonOffsetJointRoster
variable {G : Gauge}
def planted (R : Run G) {u per : ℕ} (a : Roster G) (s : Finset (Fin a.length))
    (o : Fin a.length→Site (R.family.side (u+1) per)) (i : Fin a.length)
    (z e : Site (R.family.side (u+1) per)) (part : Bool) (U : Config G (R.family.side (u+1) per)) : ℝ :=
  look part (field a (s.erase i) o U*(one a i z U-one a i e U))


end WilsonReportFrozenTraversal
end YM.Integration
