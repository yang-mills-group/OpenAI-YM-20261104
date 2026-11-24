import YM.FormalBulk08.Gorge.Sod

/-! Charge for pearl or other Taylor-resolved terms. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Gorge
open Lava Function Wick
open scoped BigOperators Classical ENNReal
variable {V I : Type*} {σ τ : ℝ} {r : ℕ} {D : Reach V} {R : Reach I}

lemma eun_tsum (F : Fin r → V → ℝ≥0∞) :
      (∑' v : chain V r,∏ i,F i (v i))=∏ i,∑' v,F i v := by
   induction r with
   | zero=> simp
   | succ r ih=>
     rw [← Equiv.tsum_eq (Fin.consEquiv (fun _:Fin (r+1)=>V)),ENNReal.tsum_prod']; simp only [Fin.consEquiv_apply]; simp_rw [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
     rw [←ih (fun i=>F i.succ),←ENNReal.tsum_mul_right]; exact tsum_congr fun v=> ENNReal.tsum_mul_left

lemma stud_tsum (F : Fin r → V → ℝ≥0∞) (a : Fin r) (x : V) :
   (∑' v : pack a x,∏ i ∈ Finset.univ.erase a,F i (v.val i))=∏ i∈Finset.univ.erase a,∑' v,F i v := by
   let G (i : Fin r) (v : V) := if i=a then (if x=v then (1:ℝ≥0∞) else 0) else F i v
   have h (v : chain V r) : ∏ i∈ Finset.univ.erase a,G i (v i)=∏ i∈ Finset.univ.erase a,F i (v i):=Finset.prod_congr rfl fun j hj=>if_neg (Finset.mem_erase.mp hj).1
   have hx : ∏ i,∑' v,G i v= ∏ i∈ Finset.univ.erase a,∑' v,F i v:= by
      rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ a), show (∑' v,G a v)=1 by simp [G,eq_comm],one_mul]; apply Finset.prod_congr rfl;intro j hj; exact tsum_congr fun i=> if_neg (Finset.mem_erase.mp hj).1
   rw [←hx,← eun_tsum];
   have hh : (∑' v : {v : chain V r // v a=x},∏ i,G i (v.val i))= ∑' v:chain V r,∏ i,G i (v i) := by
      -- tsum_subtype uses indicator
      let W := {v:chain V r | v a=x}; change (∑' v: W,(fun v:chain V r=>∏ i,G i (v i)) v.val) = _; rw [tsum_subtype W (fun v:chain V r=>∏ i,G i (v i))]; refine tsum_congr fun v=> ?_; by_cases e : v a=x
      · rw [Set.indicator_of_mem (show v∈W from e)]
      rw [Set.indicator_of_notMem (show v∉W from e)]; exact (Finset.prod_eq_zero (Finset.mem_univ a) (show G a (v a)=0 by simp [G,Ne.symm e])).symm
   rw [←hh]; refine tsum_congr fun v=>?_ ; rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ a), show G a (v.val a)=1 by simp [G,v.property],one_mul,h]

-- transmission receipt, factor out first input column, root paid per index pair
lemma towline (F : chain V r→ℝ≥0∞) (M : I) (i : Fin r) (L : I→ V→ℝ≥0∞)
      (Z : Fin r→ V→ I→ ℝ≥0∞) (U : chain V r→ V→ Fin r→ V) -- changes predictor inputs in Taylor estimate
      (A B : ℝ≥0∞) (G : Fin r→ℝ≥0∞)
      (ha : ∀ x,(∑' v:pack i x,F v.val)≤ A) (hc : (∑' x,L M x) ≤ B)
      (he : ∀ j,j ≠ i → ∀ v x, (∑' y,Z j (U v x j) y) ≤ G j) :
   (∑' t:pack i M,∑' v:chain V r,F v * L M (v i)* ∏ j ∈ Finset.univ.erase i,Z j (U v (v i) j) (t.val j)) ≤ A*B*∏ j∈Finset.univ.erase i,G j := by
    rw [ENNReal.tsum_comm,← ENNReal.tsum_fiberwise (fun v:chain V r=>_) (fun v:chain V r=>v i)]; refine le_trans (b:= (∑' x:V,A*L M x * ∏ j∈Finset.univ.erase i,G j)) (ENNReal.tsum_le_tsum fun x=>?_) ?_
    · change (∑' v: pack i x, ∑' t:pack i M, F v.val * L M (v.val i)*∏ j∈Finset.univ.erase i,Z j (U v.val (v.val i) j) (t.val j)) ≤ _
      let B':= ∏ j∈ Finset.univ.erase i,G j
      refine le_trans ?_ (mul_le_mul_left (mul_le_mul_left (ha x) _) B')
      rw [← ENNReal.tsum_mul_right,←ENNReal.tsum_mul_right];
      -- nested: rw ← first inner then again outer?
      refine ENNReal.tsum_le_tsum fun v=>?_; simp_rw [v.property]; rw [ENNReal.tsum_mul_left,stud_tsum (fun j y=>Z j (U v.val x j) y) i M]; exact mul_le_mul_right (Finset.prod_le_prod' fun j hj=> he j (Finset.mem_erase.mp hj).1 v.val x) _
    rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_left]; gcongr
end YM.FormalBulk08.Gorge
