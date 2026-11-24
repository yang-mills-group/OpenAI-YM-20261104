import YM.Integration.WilsonMeasuredPublicEntranceQuadraticGrid

/-! The finite exterior-reflection certificate spans the complete real symmetric weight-four
matrix space after two Jordan products. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceQuadraticSpan
open WilsonMeasuredPublicEntranceQuadraticGrid
open scoped Classical BigOperators

def lift:Plane ℤ→+*Plane ℝ:=(Int.castRingHom ℝ).mapMatrix
theorem at_cell (m:Plane ℤ)(i j:Six):lift m i j=(m i j:ℝ):=rfl

theorem original (S:Submodule ℝ (Plane ℝ))(unit_:(1:Plane ℝ)∈S)
    (ray:∀a b:Four,lift (exterior a b)∈S)
    (pair:∀x∈S,∀y∈S,x*y+y*x∈S){m:Plane ℝ}(symmetric:m.transpose=m):m∈S:=by
  have word (w:Word):lift (form w)∈S:=by
    induction w with
    | one=>simpa only [form,map_one] using unit_
    | ray a b=>exact ray a b
    | pair x y hx hy=>simpa only [form,map_add,map_mul] using pair _ hx _ hy
  have paid(k:BasisKey):lift (cell k)∈S:=by
    have receipt:∑t:BasisKey,(budget k t:ℝ) • lift (form (words t)) =
        (16:ℝ) • lift (cell k):=by
      ext i j
      simp only [Matrix.sum_apply,Matrix.smul_apply,at_cell,smul_eq_mul]
      exact_mod_cast exactRows k i j
    have full:(16:ℝ) • lift (cell k)∈S:=
      receipt ▸ S.sum_mem (fun t _=>S.smul_mem _ (word (words t)))
    simpa [smul_smul] using S.smul_mem (16:ℝ)⁻¹ full
  have expands:(∑k:BasisKey,m (ports k).1 (ports k).2 • lift (cell k))=m:=by
    ext i j
    simp only [Matrix.sum_apply,Matrix.smul_apply,at_cell,located,Int.cast_ite,
      Int.cast_one,Int.cast_zero,smul_eq_mul,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
      Finset.mem_univ,if_true]
    rcases covers i j with one|two
    · rw [one]
    rw [two]
    exact congrFun (congrFun symmetric i) j
  exact expands ▸ S.sum_mem (fun k _=>S.smul_mem _ (paid k))
end YM.Integration.WilsonMeasuredPublicEntranceQuadraticSpan

