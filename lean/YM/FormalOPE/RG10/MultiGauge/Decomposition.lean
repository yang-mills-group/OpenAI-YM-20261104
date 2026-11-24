import YM.FormalOPE.RG10.MultiGauge.Charter
/-!
 # Off-tree hierarchy decomposition in a blocking-compatible truss

 `Outside` reserved uses exactly bulk coordinates of the remaining truss before projection.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MultiGauge
open Function Filter Topology Set MeasureTheory PertExtension Precision
open BlockGauge Inherit Push.Loops Chart Lattice RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side}
namespace Blocking
open Fabric Stack
variable (S:StepData c f)(H:S.patch.Branches S.kernel G)(t:S.Choices)(hf:_root_.Even f.val)(L:Fabric G c)
variable (P:Inside S.ratio)(T:L.loom.Truss)
local notation "X"=> P.join T H t hf

abbrev Field {L:Fabric G n}(C:L.loom.Truss):= Direction G C.Bulk
 def Index (P:Inside S.ratio): Type:= {i:Orb.OEdge f// ¬P.Innate i}
instance : Fintype (Index S P) := Subtype.fintype _
abbrev Cross:= Direction G (Index S P)
 def indSpace : (Index S P ⊕ T.Bulk) ≃ (X).Bulk where -- precedence Sum
  toFun x:= match x with
   | .inl x=> ⟨.inl x.val,mt ((P.inner_only H t hf T _).mp) x.property⟩
   | .inr x=> ⟨.inr x.val,mt ((P.outer_only H t hf T _).mp) x.property⟩
  invFun x:= match x with
   | ⟨.inl i,h⟩=>Sum.inl (Subtype.mk i (mt ((P.inner_only H t hf T _).mpr) h))
   | ⟨.inr i,h⟩=>Sum.inr (Subtype.mk (show L.Path from i) (mt ((P.outer_only H t hf T _).mpr) h))
  left_inv x:= by cases x <;> rfl
  right_inv x:= by cases x with
                   | mk v hv=> cases v<;> rfl
 def sector : (Cross (G:=G) S P × Field T) ≃ₗ[ℝ] Field X :=
 (show (Direction G (Index S P) × Direction G T.Bulk)≃ₗ[ℝ] Direction G ((Index S P)⊕T.Bulk) from {
  toFun x i:= Sum.elim x.1 x.2 i
  invFun z:= (z∘ Sum.inl,z∘ Sum.inr)
  map_add' x y:= funext fun i=> by cases i<;>rfl
  map_smul' r u:= funext fun i=> by cases i<;>rfl
  left_inv x:= rfl
  right_inv x:= funext fun i=> by cases i<;> rfl }).trans {
   toFun x i:= x ((indSpace S H t hf L P T).symm i)
   invFun x i:= x (indSpace S H t hf L P T i)
   map_add' x y:=rfl
   map_smul' r u:=rfl
   left_inv x:= funext fun i=> congr_arg x ((indSpace S H t hf L P T).symm_apply_apply i)
   right_inv x:= funext fun i=> congr_arg x ((indSpace S H t hf L P T).apply_symm_apply i) }
end Blocking
end YM.FormalOPE.RG10.MultiGauge
