import YM.FVA2.Wick.Metric
/-!
# Dropping the ghost and antighost from the Taylor table (not just Pure false)
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick
open Function Set Finset
open MS MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.Plane MS.Book MS.Orbit MS.Orbit.Cog MS.Swirl
open scoped BigOperators Matrix Topology ContDiff
variable {A J R : Type}

section support
variable [CommRing R] {p : Sector A} {x : Raw A R}

def Alone (p : Sector A) : Submodule R (Raw A R) := fits {i|p i=false}
lemma alone_spec (h : x ∈ Alone p) : Uses {i|p i=false} x := h
lemma alone_pure (h : x ∈ Alone p) : Pure p false x := by
  intro l H
  induction l generalizing x with
  | nil => contradiction
  | cons i l ih =>
    by_cases hi:p i=true
    · exact (alone_spec h) _ i (by simp) (by simp [hi])
    exact ih (x:=D i x) ((alone_spec h).drop i) (by rw [degree_cons, show p i=false from Bool.eq_false_iff.mpr hi,Bool.false_xor] at H; exact H)
lemma alone_pair {x y : Raw A R} (h : x ∈ Alone p) (he : y∈Alone p) : product p x y∈Alone p := (alone_spec h).pair (alone_spec he)
lemma alone_mask (h : x ∈ Alone p) (k : ℤ) : mask k x ∈ Alone p:= maskUses (alone_spec h)
lemma alone_coin (p : Sector A) (z : R) : coin z ∈ Alone p := show Uses _ _ from by
  intro l i hi h
  cases l; · cases hi
  rfl
lemma alone_letter (i : A) (hi:p i=false) : atLetter i (R:=R) ∈ Alone p := (near_letter i).mono (Set.singleton_subset_iff.mpr (show i ∈ {i|p i=false} from hi))
lemma alone_D (h : x ∈ Alone p) {i:A} (hi : p i=true) : D i x=0 := (alone_spec h).off (by simp [hi])
end support

variable {i : Index A J}
local notation "b" => sector (A:=A) (J:=J)
local notation "T" => Index A J
local infixl:70 " ⋆ " => product b

section ink
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma alone_Inks (f:E→ℝ) (e:A→E) : Inks (J:=J) e f∈ Alone b := ink_uses  _ {i|b i=false} (fun j hj=> eased_p e j (by simpa using hj)) f
end ink
variable [Fintype A] [Fintype J] [DecidableEq A] [DecidableEq J]
def projection (A J : Type) [DecidableEq A] : Matrix (Index A J) (Index A J) ℂ :=
  Matrix.fromBlocks (1 : Matrix A A ℂ) 0 0 0
/-- `cut` keeps the commuting entries. -/
abbrev cut (A J : Type)[Fintype A][Fintype J][DecidableEq A] : Op (Index A J) ℂ := pull (projection A J)
local notation "P" => projection A J
local notation "Λ" => cut A J
omit [Fintype A] [Fintype J] [DecidableEq J] in
lemma cut_tie : Tie b b Pᵀ := by
  intro i j h; rcases i with i|i|i <;> rcases j with j|j|j <;> (first | rfl | exact (h rfl).elim)

omit [DecidableEq J]
lemma cutD (x : T) (v : Raw T ℂ) : D x (Λ v)= if b x then 0 else Λ (D x v) := by
  rcases x with i|i <;> rw [cut, pull_D] <;> simp [projection, sector, Fintype.sum_sum_type, Matrix.one_apply, ite_smul]
lemma cut_alone (v : Raw T ℂ) : Λ v ∈ Alone b := show Uses _ _ from by
  intro l i hi hv
  induction l generalizing v with
  | nil => cases hi
  | cons j l ih=>
    rw [D_eval j (Λ v),cutD]; split
    next h => rfl
    next h => exact ih (D j v) ((List.mem_cons.mp hi).resolve_left (fun he => hv (he.symm ▸ (show j ∈ {i:T|sector i=false} from Bool.eq_false_iff.mpr h))))
lemma alone_cut {v : Raw T ℂ}(h : v ∈ Alone b) : Λ v=v := by
  funext l; induction l generalizing v with
  | nil => rfl
  | cons i l ih=>
    rw [D_eval i (Λ v),D_eval i v,cutD]; split
    next hi=> rw [alone_D h hi]
    next _=> exact ih ((alone_spec h).drop i)
lemma cut_letter (i : T)(hi:b i=true) : Λ (atLetter i)=0 := by
  rw [cut,letter_pull]; apply Finset.sum_eq_zero; intro j _; have he : P i j=0:= by rcases i with i|i; cases hi; rcases j with j|j <;> rfl
  rw [he,zero_smul]
lemma cut_prod (x y : Raw T ℂ) : Λ (x ⋆ y) = Λ x ⋆ Λ y := pull_product cut_tie x y
end YM.FVA2.Wick
