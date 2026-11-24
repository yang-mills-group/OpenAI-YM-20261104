import YM.Integration.WilsonMeasuredPublicEntranceQuadraticTriangle
import Mathlib.Data.Matrix.Basis

/-! Signed contraction of two submitted elementary quadratic fields. The four surviving
fields share their two-point tested slot. All three spacings are kept explicitly. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceQuadraticContraction
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Stab
open WilsonMeasuredPublicEntranceQuadraticGrid WilsonMeasuredPublicEntranceQuadraticSpan
open WilsonMeasuredPublicEntranceMarkedQuadratics WilsonMeasuredPublicEntranceQuadraticProducts
open WilsonMeasuredPublicEntranceQuadraticKernel WilsonMeasuredPublicEntranceQuadraticBonds
open WilsonMeasuredPublicEntranceQuadraticWick
open scoped Classical BigOperators
variable {G:Gauge}{d:ℕ}

def strength (x y:E4):ℂ:=((4*normal*(‖x-y‖^2)⁻¹^2:ℝ):ℂ)
def fused (hd:4≤d)(D:Plane ℝ)(i i' j j':Six):HFields G d:=
  D i j • tile hd i' j'+D i j' • tile hd i' j+
    D i' j • tile hd i j'+D i' j' • tile hd i j
def card (i j:Six):Plane ℝ:=spot i j+spot j i
theorem read_card (hd:4≤d)(i j:Six):marked G hd (card i j)=(2:ℝ) • tile hd i j:=by
  rw [card,map_add,read_spot,read_spot,transpose_tile hd i j,two_smul]

private theorem single (i j:Six):spot i j=Matrix.single i j (1:ℝ):=by
  ext a b
  by_cases hi:i=a <;> by_cases hj:j=b <;> simp_all [spot,Matrix.single,eq_comm]
private theorem merge (D:Plane ℝ)(i i' j j':Six):spot i i'*D*spot j j'=D i' j • spot i j':=by
  simp only [single,Matrix.single_mul_mul_single,Matrix.smul_single,one_mul,mul_one,smul_eq_mul]

theorem purchased (hd:4≤d)(D:Plane ℝ)(sym:D.transpose=D)(i i' j j':Six):
    marked G hd (product D (card i i') (card j j'))=(2:ℝ) • fused hd D i i' j j':=by
  have flip(l m:Six):D m l=D l m:=congrFun (congrFun sym l) m
  simp only [product,card,add_mul,mul_add,merge,map_add,map_smul,read_spot]
  rw [flip i j,flip i j',flip i' j,flip i' j',
    transpose_tile hd i j,transpose_tile hd i j',transpose_tile hd i' j,
    transpose_tile hd i' j']
  simp only [fused,two_smul]
  abel

theorem original {x y z:E4}(a b:Axis){s t u:ℝ}(hs:s≠0)(ht:t≠0)(hu:u≠0)
    (xy:x-y=s • WilsonMeasuredPublicEntranceQuadraticKernel.ray a b)
    (xz:x-z=t • WilsonMeasuredPublicEntranceQuadraticKernel.ray a b)
    (yz:y-z=u • WilsonMeasuredPublicEntranceQuadraticKernel.ray a b)
    (hd:4≤d)(i i' j j' k k':Six):
    strength y z*triangle G x y z (tile hd i i').val (tile hd j j').val (tile hd k k').val=
      strength x y*strength x z*bond G y z
        (fused hd (lift (exterior a b)) i i' j j').val (tile hd k k').val:=by
  rw [WilsonMeasuredPublicEntranceQuadraticTriangle.original a b hs ht hu xy xz yz]
  simp only [fused,Submodule.coe_add,Submodule.coe_smul_of_tower,←Complex.coe_smul,
    map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,
    WilsonMeasuredPublicEntranceQuadraticBonds.original a b hu yz]
  simp only [cycle,double,beamK,strength,Complex.ofReal_mul]
  ring
end YM.Integration.WilsonMeasuredPublicEntranceQuadraticContraction

