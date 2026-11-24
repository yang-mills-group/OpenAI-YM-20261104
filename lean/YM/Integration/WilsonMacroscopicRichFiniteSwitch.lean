import YM.Integration.WilsonMacroscopicRichOriginalPortfolio

/-! An ordered expansion of the complete signed difference of two marked
products. Each summand still contains every physical partner at the same
input. The order is chosen once, independently of that input. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichFiniteSwitch
open scoped BigOperators
variable {n:ℕ}(p q:Fin n→ℂ)

def rest (i:Fin n):ℂ:=∏j∈Finset.univ.erase i,if j.val < i.val then q j else p j
private def stage (k:Fin (n+1)):ℂ:=∏j:Fin n,if j.val < k.val then q j else p j

private theorem step (i:Fin n):
    stage p q i.castSucc-stage p q i.succ=(p i-q i)*rest p q i:=by
  have before:stage p q i.castSucc=p i*rest p q i:=by
    unfold stage rest
    rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp
  have after:stage p q i.succ=q i*rest p q i:=by
    unfold stage rest
    rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Fin.val_succ,Nat.lt_succ_self,if_true]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have ne:j.val≠i.val:=fun equal=>Finset.ne_of_mem_erase hj (Fin.ext equal)
    by_cases h:j.val < i.val
    · simp [h,Nat.lt_succ_of_lt h]
    · simp [h,show ¬j.val < i.val+1 by omega]
  rw [before,after,sub_mul]

theorem original:(∏i,p i)-(∏i,q i)=∑i:Fin n,(p i-q i)*rest p q i:=by
  have telescope:∑i:Fin n,(stage p q i.castSucc-stage p q i.succ)=stage p q 0-stage p q (Fin.last n):=by
    rw [Finset.sum_sub_distrib]
    have h:=(Fin.sum_univ_castSucc (stage p q)).symm.trans (Fin.sum_univ_succ (stage p q))
    linear_combination h
  simp_rw [step p q] at telescope
  simpa only [stage,Fin.val_zero,not_lt_zero,if_false,Fin.val_last,Fin.is_lt,if_true]
    using telescope.symm

end YM.Integration.WilsonMacroscopicRichFiniteSwitch
