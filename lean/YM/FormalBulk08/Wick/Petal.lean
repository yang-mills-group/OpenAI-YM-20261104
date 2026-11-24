import YM.FormalBulk08.Wick.Slide
import YM.FormalBulk08.Wick.Spokes
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Formal Jacobian theorem at any degree: divergence of transformed integrand in the
homotopy parameter. Indices all absolute, derived letter variables in completion,
no assumption that determinant is constant. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wick
open Series PowerSeries Matrix
open scoped BigOperators
variable {R S V : Type*} [CommRing R] [CommRing S] [Algebra ℚ S] [Fintype V] [DecidableEq V]
variable [Algebra R S]

def veins (D : V→Derivation R S S) (y : V→PowerSeries S) : Matrix V V (PowerSeries S) := Matrix.of fun i j=>shaft (D j) (y i)
def roam (R : Type*) [CommRing R] [Algebra R S] (y : V→PowerSeries S) := changeBy (insertAt R y)

omit [Algebra ℚ S] [DecidableEq V] in
lemma gale (D : V→Derivation R S S) (H : Derivation R S S) (y v : V→PowerSeries S)
    (e : ∀ i,shaft H (y i)=∑ k, shaft (D k) (y i)*v k) (F : PowerSeries (Glyphs R V)) :
    shaft H (roam R y F) = ∑ i, v i * shaft (D i) (roam R y F) := by
   unfold roam; simp_rw [diff_chain,e,Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma blade [Algebra ℚ R] [IsScalarTower ℚ R S] (D : V→Derivation R S S) (H : Derivation R S S)
      (y v : V→PowerSeries S) (e : ∀ i,shaft H (y i)=∑ k,shaft (D k) (y i)*v k)
      (h : ∀ j k i,shaft (D k) (shaft (D j) (y i))=shaft (D j) (shaft (D k) (y i)))
      (g : ∀ j i,shaft (D j) (shaft H (y i))=shaft H (shaft (D j) (y i)))
      (F A : PowerSeries (Glyphs R V)) (B : PowerSeries S) (hh : shaft H B=0) (hp : coeff 0 (roam R y A-B)=0) :
      let f:=expan (roam R y A-B); let U:= (veins D y).det * f * roam R y F
      shaft H U = ∑ k, (shaft (D k) (v k * U)+shaft (D k) B * v k * U) := by
   intro f U;let J:=veins D y
   have he : shaft H J.det= ∑ k,shaft (D k) (v k*J.det) := by
     refine divergence (fun i=>shaft (D i)) _ _ v (fun i j k=>h j k i) (fun i j=>?_)
     calc _ = shaft (D j) (shaft H (y i)) := (g j i).symm
          _ = _ := by rw [e]; rfl
   let p:=roam R y F; let a:=roam R y A
   have ha : shaft H f=f*∑ i,v i * shaft (D i) a := by unfold f; rw [shaft_expan_over _ _ hp,map_sub,hh,sub_zero,gale D H y v e]
   have hx : ∀ i,shaft (D i) f=f*(shaft (D i) a-shaft (D i) B) := fun i => by unfold f; rw [shaft_expan_over _ _ hp,map_sub]
   have hy : shaft H p= ∑ i,v i * shaft (D i) p := gale D H y v e _
   change shaft H (J.det * f * p)=∑ k, (shaft (D k) (v k*(J.det*f*p))+shaft (D k) B*v k*(J.det*f*p))
   rw [Derivation.leibniz,Derivation.leibniz,hy,he,ha,smul_eq_mul,smul_eq_mul,smul_eq_mul,smul_eq_mul]
   simp_rw [Finset.mul_sum,mul_add,Finset.mul_sum, ←Finset.sum_add_distrib]
   apply Finset.sum_congr rfl; intro i _; simp only [Derivation.leibniz,hx,smul_eq_mul];ring

omit [Algebra ℚ S] in
lemma pilot (y : V → PowerSeries S) (h : V→PowerSeries S) (D : V→Derivation R S S) (hy : IsUnit (veins D y).det) :
     let v := (veins D y)⁻¹ *ᵥ h
     ∀ i,h i=∑ k,shaft (D k) (y i)*v k := by
   intro v i; change h i = ((veins D y) *ᵥ ((veins D y)⁻¹ *ᵥ h)) i
   rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hy, Matrix.one_mulVec]
end YM.FormalBulk08.Wick
