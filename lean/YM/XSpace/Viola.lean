import YM.XSpace.Canopy
/-! # Sphere table and radial chirality determinant -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Angle
open Function Set Filter Relief Season Lattice Chiral
open scoped Topology BigOperators InnerProductSpace
variable {u:E4}{g h:Season.Breeze}
abbrev spoken (v:E4): Matrix P P ℝ := fun i j=> surfT true false i j v
def lute : P→P→Axis→Axis→ℤ :=
  ![
    ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, -1]],
       ![![0, 0, 0, -1], ![0, 0, 1, 0], ![0, 1, 0, 0], ![-1, 0, 0, 0]],
       ![![0, 0, 1, 0], ![0, 0, 0, 1], ![1, 0, 0, 0], ![0, 1, 0, 0]]],
    ![![![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 0, 0]],
       ![![1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, -1]],
       ![![0, -1, 0, 0], ![-1, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0]]],
    ![![![0, 0, -1, 0], ![0, 0, 0, 1], ![-1, 0, 0, 0], ![0, 1, 0, 0]],
       ![![0, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0]],
       ![![1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, 1]]]]
set_option maxRecDepth 8000 in
private theorem luty : ∀ i j:P, ∀ a b:Axis, ∑ k:Axis,triCoeff true i a k*triCoeff false j b k=lute i j a b:= by decide
lemma lutist (i j:P)(a b:Axis):folds true false i j a b=(lute i j a b:ℝ):= by unfold folds q; exact_mod_cast luty i j a b
private theorem lutist₂ :∀ i j:P,∑ a:Axis,lute i j a a=0:=by decide
lemma lush (i j:P): ∑ a:Axis,folds true false i j a a=0:=by simp_rw [lutist]; exact_mod_cast lutist₂ i j
-- Angular transform unnormalized e_i curls
abbrev Vp (v:E4):Matrix P P ℝ:= fun i j=> ∑ a:Axis,∑ b:Axis,folds true false i j a b*(v a*v b)
local notation "Q" => Maxwell.normal
lemma basic (h:‖u‖=1)(i j:P): spoken u i j = -8*Q * Vp u i j:= by
  have hU:u≠0:= by intro q; simp [q] at h
  unfold spoken surfT Vp; simp only [Finset.sum_apply,Pi.smul_apply,hatch, smul_eq_mul,coast_at hU,Maxwell.second_Green hU,h,one_pow,inv_one,mul_one]; calc
    _ = (∑ a:Axis,∑ b:Axis,folds true false i j a b*(2*Q*basis a b))+ -8*Q* ∑ a:Axis,∑ b:Axis,folds true false i j a b*(u a*u b):=by
      simp_rw [Finset.mul_sum,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun b _=>?_ ; ring
    _ = _:= ?_
  rw [show (∑ a:Axis,∑ b:Axis,folds true false i j a b*(2*Q*basis a b))=0 from ?_,zero_add]; simp_rw [basis_eq,mul_ite]; simp only [mul_zero,mul_one,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]; rw [← Finset.sum_mul,lush,zero_mul]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 450000 in
lemma tab (u:E4): let a:=u 0; let b:=u 1; let c:=u 2; let d:=u 3; ∀ i j:P, Vp u i j =
  ![![a^2+b^2-c^2-d^2,2*(b*c-a*d),2*(b*d+a*c)],
    ![2*(a*d+b*c),a^2-b^2+c^2-d^2,2*(c*d-a*b)],
    ![2*(b*d-a*c),2*(c*d+a*b),a^2-b^2-c^2+d^2]] i j:=by
  intro w x y z i j; unfold w x y z Vp; change Fin 3 at i j; fin_cases i <;> fin_cases j <;> simp [YM.Axis,YM.XSpace.Chiral.P,lutist,lute,Fin.sum_univ_succ] <;> ring
lemma probate (u:E4): (Vp u).det=(‖u‖^2)^3:=by
  rw [Matrix.det_fin_three]; simp_rw [tab u]; rw [EuclideanSpace.real_norm_sq_eq]; simp [Fin.sum_univ_succ,Axis]; ring
abbrev magnitude := ((-8:ℝ)*Q)^3
lemma decided (h:‖u‖=1): (spoken u).det=magnitude:=by
  rw [show spoken u=((-8:ℝ)*Q) • Vp u from funext fun i=> funext fun j=> basic h i j,Matrix.det_smul]; simp [P,probate,h,magnitude]
def kit : P → P → P → ℤ:= ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
       ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
       ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]
private def k (a b:P):ℤ:= if a+1=b then 1 else 0
private theorem unto : ∀ i j l:P,k i j*k j l-k j i *k i l=kit i j l:=by decide
lemma chart (i j l:P): liftedSign i j l=(kit i j l:ℝ):=by unfold liftedSign; exact congr_arg _ (unto i j l)
private def leading (u v w:P→ℝ): ℝ:=∑ t:P,∑ m:P,∑ n:P,liftedSign m t n*(u t*v m*w n)
set_option maxRecDepth 3200 in
lemma scaling₁ (u v w:P→ℝ): leading u v w = -(Matrix.det (Matrix.of ![u,v,w])):=by unfold leading; rw [Matrix.det_fin_three]; simp [chart,kit,P,Fin.sum_univ_succ]; ring
private lemma scala (A:Matrix P P ℝ)(i j k:P):
    liftedSign i j k * leading (A i) (A j) (A k)= if liftedSign i j k=0 then 0 else -A.det:=by
  unfold P at *; rw [scaling₁]; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [chart,kit,Matrix.det_fin_three] <;> ring!
abbrev cubic (M:Matrix P P ℝ):=∑ i:P,∑ j:P,∑ k:P,liftedSign i j k*∑ t:P,∑ m:P,∑ n:P,liftedSign m t n * (M i t *M j m*M k n)
lemma cadence (M:Matrix P P ℝ): cubic M= -6 * M.det:=by
  change (∑ i:P,∑ j:P,∑ k:P,liftedSign i j k * leading _ _ _)= _; simp_rw [scala]; norm_num [chart,kit,P,Fin.sum_univ_succ]; ring
lemma negative : magnitude <0 := by unfold magnitude; rw [pow_succ, pow_succ, pow_one]; have hp: -8*Q<0:=(by linarith [Maxwell.normal_pos]); exact mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hp hp) hp
end YM.XSpace.Angle
