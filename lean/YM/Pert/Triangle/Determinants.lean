import YM.Pert.Triangle.Transfer
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Pert.Triangle
local notation "I3" => Fin 3
lemma raw_entry00 (x : Axis→ℝ) : rawPolynomial (0:I3) (0:I3) x = x 0 * x 0 * 1+x 1 * x 1 * 1+x 2 * x 2 * -1+x 3 * x 3 * -1 := by
  unfold rawPolynomial
  simp only [Fin.sum_univ_four,fanI,signRight, if_true,if_false]
  simp only [show partner 0 =⟨2,3⟩ from by decide, show partner 1 =⟨3,1⟩ from by decide, show partner 2=⟨1,2⟩ from by decide, show ternaryAxis 0=1 from by decide, show ternaryAxis 1=2 from by decide, show ternaryAxis 2=3 from by decide]
  norm_num [Fin.sum_univ_four,fanI,antisite,partner,ternaryAxis,signRight, Fin.isValue,Matrix.cons_val',Fin.reduceFinMk] <;>
    simp only [show (0:Axis)≠1 from by decide, show (0:Axis)≠2 from by decide, show (0:Axis)≠3 from by decide, show (1:Axis)≠2 from by decide, show (1:Axis)≠3 from by decide, show (2:Axis)≠3 from by decide, Ne.symm (by decide : (0:Axis)≠1),Ne.symm (by decide : (0:Axis)≠2),Ne.symm (by decide : (0:Axis)≠3),Ne.symm (by decide : (1:Axis)≠2),Ne.symm (by decide : (1:Axis)≠3),Ne.symm (by decide :(2:Axis)≠3),if_false,false_and,and_false]
  try norm_num
  all_goals ring

lemma raw_entry01 (x : Axis→ℝ) : rawPolynomial (0:I3) (1:I3) x = x 0 * x 3 * -1+x 1 * x 2 * 1+x 2 * x 1 * 1+x 3 * x 0 * -1 := by
  unfold rawPolynomial
  simp only [Fin.sum_univ_four,fanI,signRight, if_true,if_false]
  simp only [show partner 0 =⟨2,3⟩ from by decide, show partner 1 =⟨3,1⟩ from by decide, show partner 2=⟨1,2⟩ from by decide, show ternaryAxis 0=1 from by decide, show ternaryAxis 1=2 from by decide, show ternaryAxis 2=3 from by decide]
  norm_num [Fin.sum_univ_four,fanI,antisite,partner,ternaryAxis,signRight, Fin.isValue,Matrix.cons_val',Fin.reduceFinMk] <;>
    simp only [show (0:Axis)≠1 from by decide, show (0:Axis)≠2 from by decide, show (0:Axis)≠3 from by decide, show (1:Axis)≠2 from by decide, show (1:Axis)≠3 from by decide, show (2:Axis)≠3 from by decide, Ne.symm (by decide : (0:Axis)≠1),Ne.symm (by decide : (0:Axis)≠2),Ne.symm (by decide : (0:Axis)≠3),Ne.symm (by decide : (1:Axis)≠2),Ne.symm (by decide : (1:Axis)≠3),Ne.symm (by decide :(2:Axis)≠3),if_false,false_and,and_false]
  try norm_num
  all_goals ring

lemma raw_entry02 (x : Axis→ℝ) : rawPolynomial (0:I3) (2:I3) x = x 0 * x 2 * 1+x 1 * x 3 * 1+x 2 * x 0 * 1+x 3 * x 1 * 1 := by
  unfold rawPolynomial
  simp only [Fin.sum_univ_four,fanI,signRight, if_true,if_false]
  simp only [show partner 0 =⟨2,3⟩ from by decide, show partner 1 =⟨3,1⟩ from by decide, show partner 2=⟨1,2⟩ from by decide, show ternaryAxis 0=1 from by decide, show ternaryAxis 1=2 from by decide, show ternaryAxis 2=3 from by decide]
  norm_num [Fin.sum_univ_four,fanI,antisite,partner,ternaryAxis,signRight, Fin.isValue,Matrix.cons_val',Fin.reduceFinMk] <;>
    simp only [show (0:Axis)≠1 from by decide, show (0:Axis)≠2 from by decide, show (0:Axis)≠3 from by decide, show (1:Axis)≠2 from by decide, show (1:Axis)≠3 from by decide, show (2:Axis)≠3 from by decide, Ne.symm (by decide : (0:Axis)≠1),Ne.symm (by decide : (0:Axis)≠2),Ne.symm (by decide : (0:Axis)≠3),Ne.symm (by decide : (1:Axis)≠2),Ne.symm (by decide : (1:Axis)≠3),Ne.symm (by decide :(2:Axis)≠3),if_false,false_and,and_false]
  try norm_num
  all_goals ring

lemma raw_entry10 (x : Axis→ℝ) : rawPolynomial (1:I3) (0:I3) x = x 0 * x 3 * 1+x 1 * x 2 * 1+x 2 * x 1 * 1+x 3 * x 0 * 1 := by
  unfold rawPolynomial
  simp only [Fin.sum_univ_four,fanI,signRight, if_true,if_false]
  simp only [show partner 0 =⟨2,3⟩ from by decide, show partner 1 =⟨3,1⟩ from by decide, show partner 2=⟨1,2⟩ from by decide, show ternaryAxis 0=1 from by decide, show ternaryAxis 1=2 from by decide, show ternaryAxis 2=3 from by decide]
  norm_num [Fin.sum_univ_four,fanI,antisite,partner,ternaryAxis,signRight, Fin.isValue,Matrix.cons_val',Fin.reduceFinMk] <;>
    simp only [show (0:Axis)≠1 from by decide, show (0:Axis)≠2 from by decide, show (0:Axis)≠3 from by decide, show (1:Axis)≠2 from by decide, show (1:Axis)≠3 from by decide, show (2:Axis)≠3 from by decide, Ne.symm (by decide : (0:Axis)≠1),Ne.symm (by decide : (0:Axis)≠2),Ne.symm (by decide : (0:Axis)≠3),Ne.symm (by decide : (1:Axis)≠2),Ne.symm (by decide : (1:Axis)≠3),Ne.symm (by decide :(2:Axis)≠3),if_false,false_and,and_false]
  try norm_num
  all_goals ring

lemma raw_entry11 (x : Axis→ℝ) : rawPolynomial (1:I3) (1:I3) x = x 0 * x 0 * 1+x 1 * x 1 * -1+x 2 * x 2 * 1+x 3 * x 3 * -1 := by
  unfold rawPolynomial
  simp only [Fin.sum_univ_four,fanI,signRight, if_true,if_false]
  simp only [show partner 0 =⟨2,3⟩ from by decide, show partner 1 =⟨3,1⟩ from by decide, show partner 2=⟨1,2⟩ from by decide, show ternaryAxis 0=1 from by decide, show ternaryAxis 1=2 from by decide, show ternaryAxis 2=3 from by decide]
  norm_num [Fin.sum_univ_four,fanI,antisite,partner,ternaryAxis,signRight, Fin.isValue,Matrix.cons_val',Fin.reduceFinMk] <;>
    simp only [show (0:Axis)≠1 from by decide, show (0:Axis)≠2 from by decide, show (0:Axis)≠3 from by decide, show (1:Axis)≠2 from by decide, show (1:Axis)≠3 from by decide, show (2:Axis)≠3 from by decide, Ne.symm (by decide : (0:Axis)≠1),Ne.symm (by decide : (0:Axis)≠2),Ne.symm (by decide : (0:Axis)≠3),Ne.symm (by decide : (1:Axis)≠2),Ne.symm (by decide : (1:Axis)≠3),Ne.symm (by decide :(2:Axis)≠3),if_false,false_and,and_false]
  try norm_num
  all_goals ring

lemma raw_entry12 (x : Axis→ℝ) : rawPolynomial (1:I3) (2:I3) x = x 0 * x 1 * -1+x 1 * x 0 * -1+x 2 * x 3 * 1+x 3 * x 2 * 1 := by
  unfold rawPolynomial
  simp only [Fin.sum_univ_four,fanI,signRight, if_true,if_false]
  simp only [show partner 0 =⟨2,3⟩ from by decide, show partner 1 =⟨3,1⟩ from by decide, show partner 2=⟨1,2⟩ from by decide, show ternaryAxis 0=1 from by decide, show ternaryAxis 1=2 from by decide, show ternaryAxis 2=3 from by decide]
  norm_num [Fin.sum_univ_four,fanI,antisite,partner,ternaryAxis,signRight, Fin.isValue,Matrix.cons_val',Fin.reduceFinMk] <;>
    simp only [show (0:Axis)≠1 from by decide, show (0:Axis)≠2 from by decide, show (0:Axis)≠3 from by decide, show (1:Axis)≠2 from by decide, show (1:Axis)≠3 from by decide, show (2:Axis)≠3 from by decide, Ne.symm (by decide : (0:Axis)≠1),Ne.symm (by decide : (0:Axis)≠2),Ne.symm (by decide : (0:Axis)≠3),Ne.symm (by decide : (1:Axis)≠2),Ne.symm (by decide : (1:Axis)≠3),Ne.symm (by decide :(2:Axis)≠3),if_false,false_and,and_false]
  try norm_num
  all_goals ring

lemma raw_entry20 (x : Axis→ℝ) : rawPolynomial (2:I3) (0:I3) x = x 0 * x 2 * -1+x 1 * x 3 * 1+x 2 * x 0 * -1+x 3 * x 1 * 1 := by
  unfold rawPolynomial
  simp only [Fin.sum_univ_four,fanI,signRight, if_true,if_false]
  simp only [show partner 0 =⟨2,3⟩ from by decide, show partner 1 =⟨3,1⟩ from by decide, show partner 2=⟨1,2⟩ from by decide, show ternaryAxis 0=1 from by decide, show ternaryAxis 1=2 from by decide, show ternaryAxis 2=3 from by decide]
  norm_num [Fin.sum_univ_four,fanI,antisite,partner,ternaryAxis,signRight, Fin.isValue,Matrix.cons_val',Fin.reduceFinMk] <;>
    simp only [show (0:Axis)≠1 from by decide, show (0:Axis)≠2 from by decide, show (0:Axis)≠3 from by decide, show (1:Axis)≠2 from by decide, show (1:Axis)≠3 from by decide, show (2:Axis)≠3 from by decide, Ne.symm (by decide : (0:Axis)≠1),Ne.symm (by decide : (0:Axis)≠2),Ne.symm (by decide : (0:Axis)≠3),Ne.symm (by decide : (1:Axis)≠2),Ne.symm (by decide : (1:Axis)≠3),Ne.symm (by decide :(2:Axis)≠3),if_false,false_and,and_false]
  try norm_num
  all_goals ring

lemma raw_entry21 (x : Axis→ℝ) : rawPolynomial (2:I3) (1:I3) x = x 0 * x 1 * 1+x 1 * x 0 * 1+x 2 * x 3 * 1+x 3 * x 2 * 1 := by
  unfold rawPolynomial
  simp only [Fin.sum_univ_four,fanI,signRight, if_true,if_false]
  simp only [show partner 0 =⟨2,3⟩ from by decide, show partner 1 =⟨3,1⟩ from by decide, show partner 2=⟨1,2⟩ from by decide, show ternaryAxis 0=1 from by decide, show ternaryAxis 1=2 from by decide, show ternaryAxis 2=3 from by decide]
  norm_num [Fin.sum_univ_four,fanI,antisite,partner,ternaryAxis,signRight, Fin.isValue,Matrix.cons_val',Fin.reduceFinMk] <;>
    simp only [show (0:Axis)≠1 from by decide, show (0:Axis)≠2 from by decide, show (0:Axis)≠3 from by decide, show (1:Axis)≠2 from by decide, show (1:Axis)≠3 from by decide, show (2:Axis)≠3 from by decide, Ne.symm (by decide : (0:Axis)≠1),Ne.symm (by decide : (0:Axis)≠2),Ne.symm (by decide : (0:Axis)≠3),Ne.symm (by decide : (1:Axis)≠2),Ne.symm (by decide : (1:Axis)≠3),Ne.symm (by decide :(2:Axis)≠3),if_false,false_and,and_false]
  try norm_num
  all_goals ring

lemma raw_entry22 (x : Axis→ℝ) : rawPolynomial (2:I3) (2:I3) x = x 0 * x 0 * 1+x 1 * x 1 * -1+x 2 * x 2 * -1+x 3 * x 3 * 1 := by
  unfold rawPolynomial
  simp only [Fin.sum_univ_four,fanI,signRight, if_true,if_false]
  simp only [show partner 0 =⟨2,3⟩ from by decide, show partner 1 =⟨3,1⟩ from by decide, show partner 2=⟨1,2⟩ from by decide, show ternaryAxis 0=1 from by decide, show ternaryAxis 1=2 from by decide, show ternaryAxis 2=3 from by decide]
  norm_num [Fin.sum_univ_four,fanI,antisite,partner,ternaryAxis,signRight, Fin.isValue,Matrix.cons_val',Fin.reduceFinMk] <;>
    simp only [show (0:Axis)≠1 from by decide, show (0:Axis)≠2 from by decide, show (0:Axis)≠3 from by decide, show (1:Axis)≠2 from by decide, show (1:Axis)≠3 from by decide, show (2:Axis)≠3 from by decide, Ne.symm (by decide : (0:Axis)≠1),Ne.symm (by decide : (0:Axis)≠2),Ne.symm (by decide : (0:Axis)≠3),Ne.symm (by decide : (1:Axis)≠2),Ne.symm (by decide : (1:Axis)≠3),Ne.symm (by decide :(2:Axis)≠3),if_false,false_and,and_false]
  try norm_num
  all_goals ring


end YM.Pert.Triangle
