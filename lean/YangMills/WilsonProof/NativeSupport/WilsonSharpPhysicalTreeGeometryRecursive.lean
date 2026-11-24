import YangMills.WilsonProof.TreeLayout
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryConvoy
import YM.OPE.Nesting.Geometry

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open YangMills.Hierarchy Function Finset OPE OPE.Arboreal OPE.Nesting
open scoped Classical BigOperators




private theorem depth_le_sum (t : FusionTree) (a : Node t) :
    (rawTree t).depth a ≤ ∑ j : Node t, (rawTree t).depth j :=
  single_le_sum (fun j _ => Nat.zero_le ((rawTree t).depth j)) (mem_univ a)




namespace Layout
variable {t : FusionTree} {a : Node t} {T : Nesting.Tree}







private theorem unique_child {I : Type} [Fintype I] (s : OPE.Arboreal I) {v j k l : I}
    (hj : j ∈ s.kids v) (hk : k ∈ s.kids v) (jl : s.Anc j l) (kl : s.Anc k l) : j = k := by
  have one {j k : I} (hj : j ∈ s.kids v) (hk : k ∈ s.kids v) (anc : s.Anc j k) : j = k := by
    by_contra ne
    have back := anc.back (fun equal => ne equal.symm)
    have pos := s.higher hj
    rw [((s.related _ _).1 hk).2] at back
    exact (not_le_of_gt pos) back.depth
  rcases jl.compare kl with a|b
  · exact one hj hk a
  · exact (one hk hj b).symm




end Layout





end YM.Integration.WilsonSharpPhysicalTreeGeometry

