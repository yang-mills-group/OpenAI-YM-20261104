import YM.FVA2.Edges

/-!
# Slicing the old and new alphabets

These are ordinary linear changes on the Wick variables. Don't transpose a matrix using a
skew metric on ghost slots! Koszul `Raw` already has its signs in the order of differentiation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lag
open Function Set Filter Finset Matrix MS MS.Bare MS.Native MS.Koszul MS.Book MS.Orbit
open MS.Swirl MS.Cylinder Ends ArrayMap Substitute Letter MS.Cylinder.Taylor
open scoped Topology ContDiff

variable {R : Type*} {X Y X' Y' X'' Y'' : Type}

def moveL [Zero R] (A K : Matrix X X' R) (C B : Matrix Y Y' R) : Matrix (Letter X Y) (Letter X' Y') R
| a i,a j => A i j
| k i,k j => K i j
| c i,c j => C i j
| b i,b j => B i j
| _,_=>0

lemma preserves_p (A K : Matrix X X' ℂ) (C B : Matrix Y Y' ℂ) :
    Tie p p (moveL A K C B)ᵀ := by
  rintro (i|i|i|i) (j|j|j|j) h <;> first | rfl | exact (h rfl).elim

lemma compL [Semiring R] [Fintype X'] [Fintype Y']
    (A K : Matrix X X' R) (C B : Matrix Y Y' R)
    (U V : Matrix X' X'' R)(W Z : Matrix Y' Y'' R) :
    moveL A K C B * moveL U V W Z = moveL (A*U) (K*V) (C*W) (B*Z) := by
  ext i j
  rw [Matrix.mul_apply,sum_all]
  rcases i with i|i|i|i <;> rcases j with j|j|j|j <;> simp [moveL,mul_apply]

lemma alignL (A K : Matrix X X' ℝ) (C B : Matrix Y Y' ℝ) :
    intoC (moveL A K C B)= moveL (intoC A) (intoC K) (intoC C) (intoC B) := by
  ext i j
  rcases i with i|i|i|i <;> rcases j with j|j|j|j <;> rfl

lemma into_mul [Fintype Y] (A : Matrix X Y ℝ) (B : Matrix Y X' ℝ):
    intoC (A*B)=intoC A * intoC B := by ext; simp [intoC,Matrix.mul_apply]
lemma into_one [DecidableEq X] : intoC (1:Matrix X X ℝ)=1 := by ext; simp [intoC,Matrix.one_apply,apply_ite]
lemma into_transpose (A : Matrix X Y ℝ) : intoC (Aᵀ)=(intoC A)ᵀ:= rfl
lemma into_sub (A B : Matrix X Y ℝ) : intoC (A-B)=intoC A-intoC B:= by ext; simp [intoC]
lemma into_zero : intoC (0:Matrix X Y ℝ)=0:=by ext; simp [intoC]

-- view compatibility using σ = Chill K; divide to realize actual grain.
section
open Swirl
variable [Fintype X'][Fintype Y']
lemma commute_sigma (A K : Matrix X X' ℂ)(C B : Matrix Y Y' ℂ)
    (S : Matrix X' X' ℂ) (U : Matrix Y' X' ℂ) :
    moveL A K C B * sigma S U * (moveL A K C B)ᵀ=sigma (A*S*Aᵀ) (C*U*Kᵀ) := by
  ext i j
  simp_rw [Matrix.mul_apply, transpose_apply, sum_all (f:=fun _ : Letter X' Y'=>_)]
  rcases i with i|i|i|i <;> rcases j with j|j|j|j <;> simp [moveL,sigma,mul_apply]
  · simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i hi; exact Finset.sum_congr rfl fun j _ => by ring

omit [Fintype X'] [Fintype Y'] in
lemma sigma_half (S : Matrix X' X' ℂ) (U : Matrix Y' X' ℂ) :
    (show Matrix (Letter X' Y') (Letter X' Y') ℂ from Letter.grain S U)=
    (2:ℂ)⁻¹ • sigma S U:= by ext i j; unfold grain; change _=(2:ℂ)⁻¹ * _; ring

lemma commute_grain (A K : Matrix X X' ℂ)(C B : Matrix Y Y' ℂ)
    (S : Matrix X' X' ℂ)(U : Matrix Y' X' ℂ) :
    moveL A K C B * (show Matrix _ _ ℂ from grain S U) * (moveL A K C B)ᵀ=
      (grain (A*S*Aᵀ) (C*U*Kᵀ) : Matrix _ _ ℂ) := by
  rw [sigma_half S U, Matrix.mul_smul, Matrix.smul_mul, commute_sigma]; exact (sigma_half _ _).symm
end

section Bos
variable {P I : Type} {G:Gauge}
variable [Fintype Y][Fintype Y'][Fintype X][Fintype X'] [DecidableEq X] [DecidableEq X']
omit [Fintype Y'] in
lemma kin_change (L : Lot G X' →L[ℝ] Lot G X) (F : Links G X→ℝ)
    (K : Matrix (Z G X) (Z G X') ℝ) (C B : Matrix (Z G Y) (Z G Y') ℝ) (h : germ F) :
    ξ[intoC (moveL (coordinate L.toLinearMap) K C B)] (ink tangentVec F)=ink tangentVec (F ∘ L) := by
  apply ink_change _ _ _ _ L _ h; intro i; rw [sum_all];
  rcases i with i|i|i|i <;> simp only [tangentVec,moveL,map_zero,smul_zero,
    zero_smul,sum_const_zero,add_zero]
  exact coordinate_in L.toLinearMap i

omit [DecidableEq X] [DecidableEq X'] in
lemma slotK (L K : Matrix X X' ℂ) (C B : Matrix Y Y' ℂ) (x:X) :
    ξ[moveL L K C B] (atLetter (Letter.k x)) = ∑ i:X', K x i • atLetter (Letter.k i) := by
  rw [variable_form,sum_all]; simp [moveL]

omit [DecidableEq X] [DecidableEq X'] in
lemma slotC (L K : Matrix X X' ℂ) (C B : Matrix Y Y' ℂ) (x:Y) :
    ξ[moveL L K C B] (atLetter (Letter.c x)) = ∑ i:Y', C x i • atLetter (Letter.c i) := by
  rw [variable_form,sum_all]; simp [moveL]

omit [DecidableEq X] [DecidableEq X'] in
lemma slotB (L K : Matrix X X' ℂ) (C B : Matrix Y Y' ℂ) (x:Y) :
    ξ[moveL L K C B] (atLetter (Letter.b x)) = ∑ i:Y', B x i • atLetter (Letter.b i) := by
  rw [variable_form,sum_all]; simp [moveL]
end Bos
end YM.FVA2.Lag
