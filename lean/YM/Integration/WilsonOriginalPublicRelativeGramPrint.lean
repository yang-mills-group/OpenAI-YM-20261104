import YM.Integration.WilsonOriginalPublicRelativeGramJoined
import YM.Integration.WilsonOriginalPublicPivotCross

/-! Keep both independently appointed input columns, their separate mixed
earlier readings and the old scalar on the actual normalized finite film. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramPrint
open Finset Function PowerSeries Lattice RG Wilson Labels PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open Source MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonPositionProgramPublicContrast (assay)
open WilsonOriginalPublicPivotReflected (sampled)
open WilsonOriginalPublicPivotCross (col old Film detector left right)
open scoped Classical BigOperators Matrix
variable {G:Gauge}(R:Run G)(W:Initialize G){L I:Type} [Fintype L] [Fintype I]
  (h:Fin 2→ℕ)(v:(i:Fin 2)→(R.family.labels.level (h i)).Coeff)
  (X:L→Sample 2)(μ:L→ℂ)(q:ℕ)(g:ℝ)(x y:I→ℂ)(A B:I→Film W)
local notation "H" => detector W X μ q g
local notation "U" => left R W h v x A
local notation "V" => right R W h v y B

theorem faces:sampled R W h v X μ univ q g=
    assay x y (fun i j=>H (A i*B j)) +
    ((∑i,star (x i)*H (A i*V))+(∑i,y i*H (U*B i)))+
    (old R W h v X μ q g+H (U*V)):=by
  let c:I⊕I→ℂ:=Sum.elim x y
  let P:I⊕I→Film W:=Sum.elim A (fun _=>0)
  let T:I⊕I→Film W:=Sum.elim (fun _=>0) B
  simpa [assay,WilsonOriginalPublicPivotCross.left,WilsonOriginalPublicPivotCross.right,c,P,T,Fintype.sum_sum_type] using
    WilsonOriginalPublicPivotCross.spread R W h v X μ q g c P T

theorem priced (l r k:ℝ)
    (earL:‖∑i,star (x i)*H (A i*V)‖ ≤ l)(earR:‖∑i,y i*H (U*B i)‖ ≤ r)
    (deposit:‖old R W h v X μ q g+H (U*V)‖ ≤ k):
    ‖sampled R W h v X μ univ q g-assay x y (fun i j=>H (A i*B j))‖ ≤ l+r+k:=by
  rw [faces R W h v X μ q g x y A B]
  set P:=assay x y _
  set E:=∑i,star (x i)*H (A i*V)
  set D:=∑i,y i*H (U*B i)
  set C:=old R W h v X μ q g+H (U*V)
  rw [show P+(E+D)+C-P=E+D+C by abel]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add earL earR)) deposit)

theorem entry (Z C Y:Matrix I I ℂ)(i j:I):
    assay (fun k=>Z k i) (fun k=>Y k j) C=((Zᴴ*C)*Y) i j:=by
  unfold assay
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun k _=>sum_congr rfl fun l _=>by ring

end YM.Integration.WilsonOriginalPublicRelativeGramPrint
