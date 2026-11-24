import YM.Integration.WilsonMeasuredPublicEntranceQuadraticSpan

/-! The signed action and the Jordan products for the genuine coordinate and bisector
reflections determine all real symmetric two-form matrices. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceQuadraticProducts
open WilsonMeasuredPublicEntranceQuadraticGrid WilsonMeasuredPublicEntranceQuadraticSpan
open scoped Classical BigOperators

def product (D U V:Plane ℝ):Plane ℝ:=U*D*V+V*D*U

private theorem half (S:Submodule ℝ (Plane ℝ)){m:Plane ℝ}(paid:m+m∈S):m∈S:=by
  rw [←two_smul ℝ m] at paid
  simpa [smul_smul] using S.smul_mem (2:ℝ)⁻¹ paid

private theorem triple (D x y:Plane ℝ)(hD:D*D=1):
    product D (product D x 1) y+product D (product D y 1) x-
      product D (product D x y) 1=(x*y+y*x)+(x*y+y*x):=by
  simp only [product,one_mul,mul_one,add_mul,mul_add,mul_assoc]
  simp only [←mul_assoc D D _,hD,one_mul]
  abel

theorem original (S:Submodule ℝ (Plane ℝ))(signed:(1:Plane ℝ)∈S)
    (tested:∀a b:Four,∀u∈S,∀v∈S,product (lift (exterior a b)) u v∈S)
    {m:Plane ℝ}(symmetric:m.transpose=m):m∈S:=by
  apply WilsonMeasuredPublicEntranceQuadraticSpan.original S signed _ _ symmetric
  · intro a b
    apply half S
    simpa only [product,mul_one,one_mul] using tested a b 1 signed 1 signed
  intro x hx y hy
  let D:=lift (exterior 0 0)
  have exactInt:exterior 0 0 * exterior 0 0=1:=by
    ext i j
    exact (by decide : ∀i j:Six,(exterior 0 0 * exterior 0 0) i j=(1:Plane ℤ) i j) i j
  have involution:D*D=1:=by
    change lift _*lift _=1
    rw [←map_mul,exactInt,map_one]
  apply half S
  rw [←triple D x y involution]
  exact S.sub_mem (S.add_mem (tested 0 0 _ (tested 0 0 _ hx _ signed) _ hy)
    (tested 0 0 _ (tested 0 0 _ hy _ signed) _ hx)) (tested 0 0 _ (tested 0 0 _ hx _ hy) _ signed)
end YM.Integration.WilsonMeasuredPublicEntranceQuadraticProducts

