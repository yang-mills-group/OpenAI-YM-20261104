import YM.FVA2.O.Ward.Cycle
/-! Free Ward and the marked odd tree.
Parallel to the adjacent Heat.FiniteMix charge neg and Heat.Mutual.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Ward
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat
variable {R A P : Type} [AddCommGroup P] [CommRing R][Fintype A]{p:Sector A}
variable {K:Flux A P R}{F H:Row A P R}(Z:Charge p P R){B:Raw A R}
lemma negateTwin (a e:A)(q:P)(h:p e = !(p a)): -- parse
    diffPair (a,q) (e,-q) (Z.raise F)= -Z.raise (diffPair (a,q) (e,-q) F)+
     (∑ i:A, Z.table a i q • diffPair (i,q) (e,-q) F) + (∑ j:A, (cross true (p a)*Z.table e j (-q)) • diffPair (a,q) (j,-q) F):=by
    simp only [Charge.raise,diffPair_apply,Shift.deriving',Charge.hook_rule,map_add,map_sum,map_smul,field,smul_add,smul_smul,h, Finset.smul_sum]
    cases hb:p a <;> simp <;> abel
lemma skew_change (h:closed K p true)(q:P) : Z.raise (trc K q F)+trc K q (Z.raise F) = trc (Z.change K) q F := by
    simp only [trc, LinearMap.sum_apply, LinearMap.smul_apply,map_sum,map_smul]
    have he (a e:A) : K a e q • diffPair (a,q) (e,-q) (Z.raise F)= K a e q • (-Z.raise (diffPair (a,q) (e,-q) F)+
     (∑ i:A, Z.table a i q • diffPair (i,q) (e,-q) F) + (∑ j:A, (cross true (p a)*Z.table e j (-q)) • diffPair (a,q) (j,-q) F)) := by
      by_cases hh:K a e q=0; simp [hh]; rw [negateTwin]; have hw:= h a e q hh; cases he:p a <;> cases ht:p e <;> simp_all
    simp_rw [he,smul_add, Finset.smul_sum, smul_smul, Finset.sum_add_distrib,smul_neg,Finset.sum_neg_distrib]; rw [← add_assoc, ← add_assoc, add_neg_cancel, zero_add]; unfold Charge.change; simp_rw [add_smul,sum_smul,Finset.sum_add_distrib]; symm; congr 1
    · nth_rw 1 [Finset.sum_comm (f:=fun a b => ∑ i:A, (K i b q * Z.table i a q) • diffPair (a,q) (b,-q) F)]
      nth_rw 1 [Finset.sum_comm (f:=fun a b => ∑ i:A, (K a b q * Z.table a i q) • diffPair (i,q) (b,-q) F)]; apply sum_congr rfl; intro i _; rw [Finset.sum_comm]
    apply sum_congr rfl; intro i _; rw [Finset.sum_comm]; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro k _; rw [mul_left_comm]
omit [AddCommGroup P] in
lemma raise_nil (hz:∀ a (f:Mode A P→ R)(p:P),∑ b:A,Z.table a b p *(∑ c:A,Z.table b c p * f (c,p))=0): Z.raise (Z.raise F)=0:= by
    ext l; change _ = 0; induction l generalizing F with
    | nil=> exact Shift.nil ..
    | cons i l ih=>
      rcases i with ⟨i,q⟩; rw [Z.act_at, show D (i,q) (Z.raise F)= (∑ b, Z.table i b q • D (b,q) F)+ (cross true (p i) : R) • Z.raise (D (i,q) F) from (Z.move.deriving' _ F).trans (congr_arg (· + _) (Z.hook_rule F i q))]
      simp only [map_add,map_smul,map_sum,Finset.sum_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul,ih,Z.act_at F]
      rw [mul_zero,add_zero]; simp_rw [mul_add,sum_add_distrib]; rw [show ∑ b,Z.table i b q * (∑ c,Z.table b c q*F ((c,q)::l))=0 from hz i (fun a=> F (a::l)) q,zero_add,Finset.mul_sum, ← sum_add_distrib]; refine sum_eq_zero fun k _=>?_
      by_cases h: Z.table i k q=0; simp [h]; rw [Z.from_opposite _ _ _ h]; cases hj:p i <;> simp
end YM.FVA2.O.Ward
