import YM.Pert.Triangle.Invariance
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Pert.Triangle
local notation "I3" => Fin 3
def loopSum (κ s:ℝ) (A:Matrix I3 I3 ℝ) (i j k : I3) :=
  (∑ m:I3,∑ n:I3, ((κ*A j m) * (κ*A k n)) * (∑ t, κ*A i t * (eps3 m t n:ℝ) * s))
def sixPoly (v z w : I3→ℝ) := v 0 * z 1 * w 2 + v 1 * z 2 * w 0 + v 2 * z 0 * w 1 - v 1*z 0*w 2-v 0*z 2*w 1-v 2*z 1*w 0
lemma loop_expand (κ s:ℝ) (A:Matrix I3 I3 ℝ) (i j k : I3) : loopSum κ s A i j k = -κ^3 * s * sixPoly (A i) (A j) (A k):= by
  unfold loopSum sixPoly
  norm_num [Fin.sum_univ_three,eps3, Int.cast_ite, Fin.reduceFinMk]
  all_goals try simp only [show (0:I3)+2=2 from by decide, show (0:I3)+3=0 from by decide, show (1:I3)+2=0 from by decide, show (1:I3)+3=1 from by decide, show (2:I3)+2=1 from by decide, show (2:I3)+3=2 from by decide, show (1:I3)+1=2 from by decide,show (2:I3)+1=0 from by decide,show (0:I3) ≠2 from by decide, show (0:I3)≠1 from by decide,show (1:I3)≠2 from by decide,show (1:I3) ≠0 from by decide, show (2:I3)≠0 from by decide,show (2:I3)≠1 from by decide,if_false,if_true,false_and,and_false, true_and, and_true]
  all_goals try simp only [if_pos (rfl: (2:I3)=2), if_pos (rfl: (1:I3)=1), if_pos (rfl: (0:I3)=0)]
  all_goals ring

lemma epsilon_poly (A:Matrix I3 I3 ℝ) (i j k:I3) : sixPoly (A i) (A j) (A k) = eps3 i j k * A.det := by
  have num : ∀i j k, (fun q:ℤ=>(q:ℝ)) (eps3 i j k) = ((eps3 i j k):ℝ) := by intros; rfl
  rw [Matrix.det_fin_three]; unfold sixPoly
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num [Fin.sum_univ_three,eps3, Int.cast_ite, Fin.reduceFinMk]
  all_goals try simp only [show (0:I3)+2=2 from by decide, show (0:I3)+3=0 from by decide, show (1:I3)+2=0 from by decide, show (1:I3)+3=1 from by decide, show (2:I3)+2=1 from by decide, show (2:I3)+3=2 from by decide, show (1:I3)+1=2 from by decide,show (2:I3)+1=0 from by decide,show (0:I3) ≠2 from by decide, show (0:I3)≠1 from by decide,show (1:I3)≠2 from by decide,show (1:I3) ≠0 from by decide, show (2:I3)≠0 from by decide,show (2:I3)≠1 from by decide,if_false,if_true,false_and,and_false, true_and, and_true]
  all_goals try simp only [if_pos (rfl: (2:I3)=2), if_pos (rfl: (1:I3)=1), if_pos (rfl: (0:I3)=0)]
  all_goals try simp only [Fin.eta]
  all_goals try norm_num [Fin.ext_iff]
  all_goals try simp [Fin.ext_iff]
  all_goals ring
lemma triple_inner (κ s:ℝ) (A:Matrix I3 I3 ℝ) (i j k : I3) : loopSum κ s A i j k = κ^3 * s * (-(eps3 i j k: ℝ) * A.det) := by rw [loop_expand,epsilon_poly];ring

end YM.Pert.Triangle
