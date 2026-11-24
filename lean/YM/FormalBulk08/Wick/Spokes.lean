import YM.FormalBulk08.Series.Level
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Divergence of the formal Jacobian. Uses only finite algebra. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wick
open Series Function Matrix
open scoped BigOperators
variable {R S V : Type*} [CommRing S] [CommRing R] [Algebra R S]
lemma gauge_prod [DecidableEq V] (D : Derivation R S S) (f : V → S) (v : Finset V) :
    D (∏ i∈v,f i) = ∑ j∈v, D (f j) * ∏ k∈v.erase j, f k := by
   induction v using Finset.induction_on with
   | empty=> simp
   | insert a v ha hv=>
     rw [Finset.prod_insert ha,Derivation.leibniz,hv,smul_eq_mul,smul_eq_mul,Finset.mul_sum, Finset.sum_insert ha, Finset.erase_insert ha,add_comm,mul_comm _ (D _)]
     congr 1; apply Finset.sum_congr rfl; intro i hi; rw [Finset.erase_insert_of_ne (Ne.symm (ne_of_mem_of_not_mem hi ha)), Finset.prod_insert (by simp_all)];ring

variable [DecidableEq V] [Fintype V]
lemma stem_scan (D : Derivation R S S) (J : Matrix V V S) : D J.det= ∑ i, det (J.updateCol i fun j=>D (J j i)) := by
   simp_rw [det_apply',map_sum,Derivation.leibniz,smul_eq_mul]
   have h (i : ℤ) : D (i : S)=0 := by rw [← _root_.map_intCast (algebraMap R S),Derivation.map_algebraMap]
   simp_rw [h, gauge_prod D, Finset.mul_sum,mul_zero,add_zero]; rw [Finset.sum_comm]
   apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro p _; congr 1
   rw [← Finset.mul_prod_erase Finset.univ (fun i=>updateCol J a (fun j=>D (J j a)) (p i) i) (Finset.mem_univ a),updateCol_self]
   congr 1; apply Finset.prod_congr rfl; intro i hi; simp [Finset.ne_of_mem_erase hi]

def spanCol (J : Matrix V V S) (j : V) : (V → S) →ₗ[S] S where
   toFun U := (J.updateCol j U).det
   map_add' _ _ := det_updateCol_add ..
   map_smul' _ _ := det_updateCol_smul ..
lemma det_updateCol_shot (J : Matrix V V S) (i : V) (P : V → V → S) : det (J.updateCol i (∑ j,P j))=∑ j, det (J.updateCol i (P j)) := map_sum (spanCol J i) P _

/-- Formal time divergence. `U` already solves the pull velocity equation. No
      assertion about volume preservation at nonzero coupling. -/
lemma divergence (D : V → Derivation R S S) (E : Derivation R S S) (J : Matrix V V S) (U : V→S)
    (sym : ∀ i j k,D k (J i j)=D j (J i k)) (e : ∀ i j,E (J i j)=D j (∑ k,J i k*U k)) :
   E J.det = ∑ i,D i (U i*J.det) := by
    have he (j : V) : (fun i=> E (J i j))=(fun i => ∑ k, (D j (U k)) • J i k) + ∑ k,U k • fun i=> D k (J i j) := by
       ext1 i; rw [e i j]; simp_rw [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,map_sum,Derivation.leibniz,smul_eq_mul,←Finset.sum_add_distrib]
       apply Finset.sum_congr rfl; intro k _; rw [sym i]; ring
    rw [stem_scan]; simp_rw [he,det_updateCol_add, det_updateCol_sum, det_updateCol_shot,det_updateCol_smul,Derivation.leibniz,smul_eq_mul,Finset.sum_add_distrib];
    rw [Finset.sum_comm,add_comm];simp_rw [stem_scan,Finset.mul_sum];
    simp_rw [mul_comm J.det]
end YM.FormalBulk08.Wick
