import YM.Integration.WilsonPublicOutputSmooth
import YM.Integration.WilsonPublicOutputRows

/-! Compare the actual signed three-field row and each two-field column with
the independent tables at their true prescribed finite detector value. The
coefficient salaries are the actual coordinates of the MS experiment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourFiniteSlate
open Table Spec RG17 Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register WilsonMSDictionaryVector
open private sum_error from YM.Integration.WilsonPublicOutputRows
open scoped Classical BigOperators
variable {G:Gauge}{C:Family G}{I:Type}[Fintype I]{S:Table C.book}{f:Extraction.Order}(F:Final C f S)

private theorem split {A D:Type}[Fintype D][NormedAddCommGroup A][NormedSpace ℂ A]
    (a:D→ℂ)(gram truth:D→A)(x y:A):
    ‖x-∑i,a i • truth i‖ ≤ ‖x-y‖+‖y-∑i,a i • gram i‖+∑i,‖a i‖*‖gram i-truth i‖:=by
  let m:=∑i,a i • gram i
  let v:=∑i,a i • truth i
  have h1:=norm_sub_le_norm_sub_add_norm_sub x m v
  have h2:=norm_sub_le_norm_sub_add_norm_sub x y m
  exact h1.trans (add_le_add h2 (sum_error a gram truth))

def invoice (X:I→External C S)(pub:Free C 4≃ₗ[ℂ]S.Field 4)(value:Free C 4)
    (observed joint:I→ℂ)(gram:Dframe.Toon G 4→I→ℂ):ℝ:=
  let a:=(WilsonMSDictionaryVector.basis C 4).repr value
  ‖observed-joint‖ + ‖joint-∑b,a b • gram b‖ +
    ∑b,‖a b‖*‖gram b-fun j=>(X j).charge F 4 (pub (WilsonMSDictionaryVector.basis C 4 b))‖

theorem original (X:I→External C S)(pub:Free C 4≃ₗ[ℂ]S.Field 4)(value:Free C 4)
    (observed joint:I→ℂ)(gram:Dframe.Toon G 4→I→ℂ):
    ‖observed-(fun j=>(X j).charge F 4 (pub value))‖≤ invoice F X pub value observed joint gram:=by
  let T:Free C 4→ₗ[ℂ](I→ℂ):=(LinearMap.pi (fun j=>(X j).charge F 4)).comp pub.toLinearMap
  let b:=WilsonMSDictionaryVector.basis C 4
  let a:=b.repr value
  have formula:T value=∑i,a i • T (b i):=by
    conv_lhs=>rw [←b.sum_repr value]
    simp only [map_sum,map_smul]
    rfl
  change ‖observed-T value‖≤‖observed-joint‖+‖joint-∑i,a i • gram i‖+
    ∑i,‖a i‖*‖gram i-T (b i)‖
  rw [formula]
  exact split (fun i=>a i) gram (fun i=>T (b i)) observed joint

end YM.Integration.WilsonCenteredFourFiniteSlate
