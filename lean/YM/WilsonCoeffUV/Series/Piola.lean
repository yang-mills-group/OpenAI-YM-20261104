import YM.WilsonCoeffUV.Series.Xadic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Formal Piola and algebraic pullback of densities. Spectator Y-Aux held fixed,
uses only its motion if stipulated. These lemmas are over the filtered ring. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Function Matrix PowerSeries Finset
open scoped BigOperators
variable {U Y : Type*}
section alg
variable {R : Type*} [CommRing R][Algebra ℝ R] [Fintype U] [DecidableEq U]

omit [Fintype U] in
private lemma Dprod (d:Derivation ℝ R R) (p:U→R)(s:Finset U) : d (∏ i∈s,p i)=∑ i∈s,d (p i)*∏ j∈s.erase i,p j := by
  induction s using Finset.induction_on with
  | empty=> simp
  | @insert k s hk e=>
    rw [prod_insert hk, Derivation.leibniz,e,sum_insert hk, erase_insert hk,smul_eq_mul,smul_eq_mul,add_comm, mul_comm _ (d _)]
    rw [Finset.mul_sum]; congr 1
    apply sum_congr rfl; intro i hi
    have hh := ne_of_mem_of_not_mem hi hk
    rw [Finset.erase_insert_of_ne hh.symm,prod_insert]; ring; exact notMem_mono (erase_subset _ _) hk

lemma Ddet (d:Derivation ℝ R R) (A:Matrix U U R) : d A.det = ∑ j,∑ i,A.adjugate j i * d (A i j) := by
  have he : d A.det=∑ k, (updateCol A k (fun i=>d (A i k))).det := by
    simp_rw [Matrix.det_apply']
    rw [map_sum];
    rw [sum_comm]; apply sum_congr rfl; intro σ _
    simp only [Derivation.leibniz,Dprod,smul_eq_mul,mul_sum]
    rw [show d (↑(↑(Equiv.Perm.sign σ) : ℤ):R)=0 from by simp,mul_zero, add_zero]
    apply sum_congr rfl; intro i _
    congr 1; rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ i), updateCol_self]; congr 1
    exact prod_congr rfl fun j hj=> by rw [updateCol_ne (mem_erase.mp hj).1]
  rw [he]; apply sum_congr rfl; intro k _; rw [← cramer_apply,cramer_eq_adjugate_mulVec]; rfl

omit [DecidableEq U] in
private lemma rule (d:Derivation ℝ R R) (A B:Matrix U U R): (A*B).map d=(A.map d)*B+A*B.map d := by
  ext i j; simp_rw [Matrix.add_apply,map_apply,Matrix.mul_apply,map_apply,map_sum, Derivation.leibniz,smul_eq_mul,Finset.sum_add_distrib]; rw [add_comm]; congr 1; apply Finset.sum_congr rfl; intro a _; rw [mul_comm]
private lemma marker_rule (A:Matrix U U R)(d:Derivation ℝ R R) : A.det • ((adjugate A).map d)= d A.det • (adjugate A) - adjugate A*(A.map d)*adjugate A := by
  have he := congrArg (fun B:Matrix U U R=>B.map d) A.mul_adjugate
  change (A*A.adjugate).map d = _ at he
  have hv : (A.det • (1:Matrix U U R)).map d = d A.det • (1:Matrix U U R) := by ext i j; by_cases h:i=j<;>simp [h]
  rw [rule,hv] at he
  have hh := congrArg (adjugate A * ·) he
  rw [mul_add,←mul_assoc,←mul_assoc,adjugate_mul, mul_smul_comm,mul_one,smul_mul_assoc,one_mul] at hh
  apply eq_sub_of_add_eq; rw [add_comm]; exact hh

/-- Piola identity for X-coordinate formal derivatives (version with unit
Jacobian determinant after dropping scaling). -/
lemma piol (D:U→Derivation ℝ R R)(A:Matrix U U R)(h:IsUnit A.det)
    (he:∀ i j k,D k (A i j)=D j (A i k))(u:U) : ∑ j,D j (adjugate A j u)=0 := by
  apply h.mul_right_inj.mp
  rw [mul_sum,mul_zero]
  have hy j : A.det * D j (adjugate A j u) = D j A.det * adjugate A j u - (adjugate A*(A.map (D j))*adjugate A) j u := congr_fun (congr_arg (fun M : Matrix U U R=>M j) (marker_rule A (D j))) u
  simp_rw [hy,Finset.sum_sub_distrib,Ddet,Finset.sum_mul,Matrix.mul_apply, map_apply]; rw [sub_eq_zero,Finset.sum_comm];
  apply sum_congr rfl; intro a _
  simp_rw [Finset.sum_mul]
  apply sum_congr rfl; intro b _; apply sum_congr rfl; intro c _
  rw [he]
end alg
end YM.WilsonCoeffUV.Blue
