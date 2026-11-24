import YM.Integration.WilsonMeasuredPublicEntranceQuadraticContraction

/-! Polarization of the three measured insertions on actual signed real quadratic
labels. The unhalved Jordan product carries a factor of two. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceQuadraticPolarization
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Stab
open WilsonMeasuredPublicEntranceQuadraticGrid WilsonMeasuredPublicEntranceQuadraticSpan
open WilsonMeasuredPublicEntranceMarkedQuadratics WilsonMeasuredPublicEntranceQuadraticProducts
open WilsonMeasuredPublicEntranceQuadraticContraction
open scoped Classical BigOperators
variable {G:Gauge}{d:ℕ}

theorem cards {U:Plane ℝ}(sym:U.transpose=U):U=∑i,∑j,(U i j/2) • card i j:=by
  ext a b
  have flip:U b a=U a b:=congrFun (congrFun sym a) b
  simp [card,spot,smul_add,Finset.sum_add_distrib,Matrix.sum_apply,Matrix.smul_apply,
    smul_eq_mul,mul_ite,flip]

theorem agree {E:Type*}[AddCommMonoid E][Module ℝ E]
    (L R:Plane ℝ→ₗ[ℝ] E)(h:∀i j,L (card i j)=R (card i j)){U:Plane ℝ}
    (sym:U.transpose=U):L U=R U:=by
  rw [cards sym]
  simp only [map_sum,map_smul,h]

def third (hd:4≤d)(x y z:E4)(w:WickPol G)(c:ℂ):Plane ℝ→ₗ[ℝ] Plane ℝ→ₗ[ℝ] ℂ:=
  LinearMap.mk₂ ℝ (fun U V=>c*triangle G x y z (marked G hd U).val (marked G hd V).val w)
    (fun _ _ _=>by simp [mul_add]) (fun _ _ _=>by
      simp only [map_smul,Submodule.coe_smul_of_tower,←Complex.coe_smul,map_smul,
        LinearMap.smul_apply,smul_eq_mul];ring)
    (fun _ _ _=>by simp [mul_add]) (fun _ _ _=>by
      simp only [map_smul,Submodule.coe_smul_of_tower,←Complex.coe_smul,map_smul,
        LinearMap.smul_apply,smul_eq_mul];ring)
private theorem add_left (D U V W:Plane ℝ):
    product D (U+V) W=product D U W+product D V W:=by
  simp only [product,add_mul,mul_add]
  abel
private theorem add_right (D U V W:Plane ℝ):
    product D U (V+W)=product D U V+product D U W:=by
  simp only [product,add_mul,mul_add]
  abel
def second (hd:4≤d)(y z:E4)(D:Plane ℝ)(w:WickPol G)(c:ℂ):
    Plane ℝ→ₗ[ℝ] Plane ℝ→ₗ[ℝ] ℂ:=
  LinearMap.mk₂ ℝ (fun U V=>c*bond G y z (marked G hd (product D U V)).val w)
    (fun _ _ _=>by simp [add_left,mul_add])
    (fun _ _ _=>by simp only [product,smul_mul_assoc,mul_smul_comm,←smul_add,map_smul,
      Submodule.coe_smul_of_tower,←Complex.coe_smul,map_smul,LinearMap.smul_apply,smul_eq_mul];ring)
    (fun _ _ _=>by simp [add_right,mul_add])
    (fun _ _ _=>by simp only [product,smul_mul_assoc,mul_smul_comm,←smul_add,map_smul,
      Submodule.coe_smul_of_tower,←Complex.coe_smul,map_smul,LinearMap.smul_apply,smul_eq_mul];ring)

theorem original {x y z:E4}(a b:Axis){s t u:ℝ}(hs:s≠0)(ht:t≠0)(hu:u≠0)
    (xy:x-y=s • WilsonMeasuredPublicEntranceQuadraticKernel.ray a b)
    (xz:x-z=t • WilsonMeasuredPublicEntranceQuadraticKernel.ray a b)
    (yz:y-z=u • WilsonMeasuredPublicEntranceQuadraticKernel.ray a b)
    (hd:4≤d)(U V:Plane ℝ)(sU:U.transpose=U)(sV:V.transpose=V)(k l:Six):
    strength y z*triangle G x y z (marked G hd U).val (marked G hd V).val (tile hd k l).val=
      (2*strength x y*strength x z)*bond G y z
        (marked G hd (product (lift (exterior a b)) U V)).val (tile hd k l).val:=by
  let D:=lift (exterior a b)
  have ds:D.transpose=D:=by
    ext i j
    exact congrArg (fun k:ℤ=>(k:ℝ)) ((by decide:∀a b:Axis,∀i j:Six,exterior a b j i=exterior a b i j) a b i j)
  let L:=third (G:=G) hd x y z (tile hd k l).val (strength y z)
  let R:=second (G:=G) hd y z D (tile hd k l).val (2*strength x y*strength x z)
  change L.flip V U = R.flip V U
  apply agree (L.flip V) (R.flip V) _ sU
  intro i i'
  change L (card i i') V=R (card i i') V
  apply agree _ _ _ sV
  intro j j'
  change strength y z*triangle G x y z (marked G hd (card i i')).val (marked G hd (card j j')).val _=
    _*bond G y z (marked G hd (product D (card i i') (card j j'))).val _
  rw [read_card,read_card,purchased hd D ds]
  simp only [Submodule.coe_smul_of_tower,←Complex.coe_smul,map_smul,LinearMap.smul_apply,smul_eq_mul,
    Complex.ofReal_ofNat]
  linear_combination 4*WilsonMeasuredPublicEntranceQuadraticContraction.original (G:=G) a b hs ht hu xy xz yz hd i i' j j' k l
end YM.Integration.WilsonMeasuredPublicEntranceQuadraticPolarization

