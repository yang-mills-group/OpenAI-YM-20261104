import YM.AveragedStep.Recursion.Cone
/- Sum arithmetic used in recursion. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.SD
open scoped Topology BigOperators Classical
open Finset
lemma range_conv (d:ℕ)(L : ℕ → ℕ → ℝ):
   ∑ n ∈ range (d+1), (∑ j∈active n,L j (n-j))=
   ∑ j ∈ active d, (∑ m ∈ range (d-j+1),L j m):=by
 induction d with
 | zero=> simp [active]
 | succ d ih=>
   rw [sum_range_succ,ih]
   have h : active (d+1) = insert (d+1) (active d):= by ext i; simp [active]; omega
   rw [h,sum_insert (by simp [active]),sum_insert (by simp [active])]
   simp only [Nat.sub_self,zero_add,Finset.range_one,Finset.sum_singleton]
   rw [show (∑ j∈active d,∑ m∈range (d+1-j+1),L j m)= (∑ j∈active d,∑ m∈range (d-j+1),L j m)+ ∑ j∈active d,L j (d+1-j) from ?_]; ring
   rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j hj; obtain ⟨hp,hl⟩ := on_tape _ _ |>.mp hj
   rw [sum_range_succ,show d+1-j=d-j+1 from by omega]
lemma active_power (d:ℕ)(t:ℝ)(L : ℕ → ℕ → ℝ):
   ∑ n ∈ range (d+1), t^n * (∑ j∈active n,L j (n-j))=
   ∑ j ∈ active d, t^j * (∑ m ∈ range (d-j+1),t^m * L j m):=by
 rw [show (∑ n ∈ range (d+1), t^n*(∑ j∈active n,L j (n-j)))= _ from Eq.trans ?_ (range_conv d (fun i j=> t^i*(t^j*L i j)))]
 · simp only [mul_sum]
 apply Finset.sum_congr rfl; intro n hn; rw [mul_sum]; apply Finset.sum_congr rfl; intro j hj; obtain ⟨hp,hl⟩:= (on_tape _ _).mp hj
 rw [← mul_assoc,← pow_add, show j+(n-j)=n by omega]
end YM.AveragedStep.SD
