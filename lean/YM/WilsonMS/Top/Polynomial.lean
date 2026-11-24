import YM.MS.Swirl.Cut

/-!
# Working at one coefficient of LPT

Use **the input algebra to the MS removal theorem** (graded-symmetric
Taylor symbols in left-derivative convention). Some tools for treating these
as polynomials. In particular we will use acyclicity of an odd *linear*
differential; the contraction for that calculation should only have to be
specified on the fields, not on all ranks of vertices.
-/

set_option autoImplicit false
noncomputable section

namespace YM.WilsonMS

open MS MS.Koszul MS.Cylinder MS.Book Finset
variable {A : Type} {p : Sector A} {F H : Raw A ℂ} {n : ℕ}

lemma rank_limit {h : ℤ} (hr : Book.rank h F) : Limit F h := fun l hl =>
  hr l
    (by
      rw [mod_int]
      omega)

lemma limit_zero_coin (hF : Limit F 0) : F = coin (F []) := by
  ext l
  cases l with
  | nil => rfl
  | cons i l => exact hF (i :: l) (by simp)

lemma mask_symmetric (r : ℤ) (hF : Symm p F) : Symm p (mask r F) := by
  intro l i j t
  have he : (l ++ i :: j :: t).length = (l ++ j :: i :: t).length := by simp
  by_cases h : ((l ++ j :: i :: t).length : ℤ) = r
  · rw [enough _ h,
      enough _
        (by
          rw [he]
          exact h),
      hF l i j t]
  rw [strange _ h,
    strange _
      (by
        rw [he]
        exact h),
    mul_zero]

lemma limit_sub_mask (hF : Limit F (n + 1 : ℕ)) : Limit (F - mask (n + 1 : ℕ) F) n := by
  intro l hl
  by_cases h : (l.length : ℤ) = (↑(n + 1 : ℕ) : ℤ)
  · rw [Pi.sub_apply, enough _ h, sub_self]
  rw [Pi.sub_apply, strange _ h, hF l (by omega), sub_zero]

lemma rank_euler [Fintype A] (h : Symm p F) (r : Book.rank n F) :
    (n : ℂ) • F = ∑ a : A, product p (atLetter a) (D a F) := by
  classical
  have H : MS.Swirl.Tick (fun _ : A => 1) F = (n : ℂ) • F := by
    ext l
    by_cases he : l.length = n
    · change (l.map (fun _ => (1 : ℂ))).sum * F l = (n : ℂ) * F l
      have hx (l : List A) : (l.map (fun _ => (1 : ℂ))).sum = (l.length : ℂ) := by
        induction l with
        | nil => simp
        | cons i l ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
          push_cast
          ring
      rw [hx, he]
    change (l.map (fun _ => (1 : ℂ))).sum * F l = (n : ℂ) * F l
    rw [r l
        (by
          rw [mod_int]
          omega),
      mul_zero, mul_zero]
  rw [← H, MS.Swirl.overture _ h]
  simp only [one_smul]

/-- Act on a symbol by replacing the letters (we'll specify a degree-one
polynomial on each letter, so in particular this will preserve rank). -/
def vectorField [Fintype A] (p : Sector A) (s : A → Raw A ℂ) : Op A ℂ :=
  ∑ a : A, (product p (s a)).comp (D a)

/-- Parity and arity conditions on a linear odd vector field. -/
structure OddField (p : Sector A) (s : A → Raw A ℂ) : Prop where
  rank a : Book.rank 1 (s a)
  odd a : Pure p (!(p a)) (s a)

variable [Fintype A] {s t : A → Raw A ℂ}

section derivation

lemma vectorField_eq (p : Sector A) (s : A → Raw A ℂ) (F : Raw A ℂ) :
    vectorField p s F = ∑ a : A, product p (s a) (D a F) := by
  simp only [vectorField, LinearMap.sum_apply, LinearMap.comp_apply]

lemma vectorField_letter (p : Sector A) (s : A → Raw A ℂ) (i : A) :
    vectorField p s (atLetter i) = s i := by
  classical
  rw [vectorField_eq, Finset.sum_eq_single_of_mem i (mem_univ i), hear, ← (coin_pure 1).central,
    coin_product, one_smul]
  intro j _ hj
  rw [unheard i hj, map_zero]

lemma vectorField_coin (p : Sector A) (s : A → Raw A ℂ) (x : ℂ) : vectorField p s (coin x) = 0 := by
  rw [vectorField_eq]
  exact sum_eq_zero (fun a _ => by rw [show D a (coin x) = 0 from rfl, map_zero])

lemma rank_one_symm {A : Type} (p : Sector A) {F : Raw A ℂ} (h : Book.rank 1 F) : Symm p F := by
  intro l a b t
  rw [h (l ++ a :: b :: t) ?_, h (l ++ b :: a :: t) ?_, mul_zero] <;>
    ( rw [mod_int]
      simp only [List.length_append, List.length_cons, Nat.cast_add, Nat.cast_one]
      omega)

lemma OddField.symmetric (h : OddField p s) (hF : Symm p F) : Symm p (vectorField p s F) := by
  rw [vectorField_eq]
  exact Symm.sum _ (fun i _ => (rank_one_symm _ (h.rank i)).times (hF.drop i))

lemma OddField.keepsRank {r : ℤ} (h : OddField p s) (hF : Book.rank r F) :
    Book.rank r (vectorField p s F) := by
  rw [vectorField_eq]
  apply Rails.sum
  intro i _
  nth_rw 1 [show r = 1 + (r - 1) by omega]
  exact (h.rank i).product (hF.enter i)

local infixl:70 " ⋄ " => product p

private lemma signs_pass (i b : Bool) : (cross i b : ℂ) * cross (!i) b = cross true b := by
  cases i <;> cases b <;> simp

lemma OddField.derives {b : Bool} (h : OddField p s) (hF : Pure p b F) (U : Raw A ℂ) :
    vectorField p s (F ⋄ U) =
      (vectorField p s F) ⋄ U + (cross true b : ℂ) • (F ⋄ vectorField p s U) := by
  rw [vectorField_eq, vectorField_eq, vectorField_eq]
  simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [D_product, hF.signs, map_add, ← times_assoc, ← times_assoc, map_smul, map_smul,
    LinearMap.smul_apply, (h.odd i).times_comm hF, map_smul, LinearMap.smul_apply, smul_smul,
    signs_pass, times_assoc F]

/-- Anti-commutator acts on grade-n by n, if it acts by identity on the letters. -/
lemma anticommutator (hs : OddField p s) (ht : OddField p t)
    (h : ∀ i, vectorField p s (t i) + vectorField p t (s i) = atLetter i) (hF : Book.rank n F)
    (H : Symm p F) :
    ((vectorField p s).comp (vectorField p t) + (vectorField p t).comp (vectorField p s)) F =
      (n : ℂ) • F := by
  induction n generalizing F with
  | zero =>
    have he : F = coin (F []) := limit_zero_coin (rank_limit (by exact_mod_cast hF))
    rw [he]
    simp [vectorField_coin]
  | succ n ih =>
    let T := ((vectorField p s).comp (vectorField p t) + (vectorField p t).comp (vectorField p s))
    have ha i (F' : Raw A ℂ) :
      T (product p (atLetter i) F') = product p (atLetter i) F' + product p (atLetter i) (T F') := by
      unfold T
      simp only [LinearMap.add_apply, LinearMap.comp_apply, hs.derives (speaks_p i),
        ht.derives (speaks_p i), vectorField_letter, map_add, map_smul, hs.derives (ht.odd i),
        ht.derives (hs.odd i)]
      have hv := congr_arg (fun f => product p f F') (h i)
      simp only [map_add, LinearMap.add_apply] at hv
      rw [← hv]
      cases hx : p i <;>
          simp only [Bool.not_false, Bool.not_true, cross_true, cross_false', one_smul,
            neg_one_smul] <;>
        abel
    apply
      (smul_right_injective (Raw A ℂ) (r := ((n + 1 : ℕ) : ℂ)) (by exact_mod_cast Nat.succ_ne_zero n))
    change ((↑(n + 1 : ℕ)) : ℂ) • T F = (↑(n + 1 : ℕ) : ℂ) • (↑(n + 1 : ℕ) : ℂ) • F
    rw [← map_smul T, rank_euler H hF, map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hf : Book.rank n (D i F) := by
      convert hF.enter i using 1
      omega
    rw [ha, show T (D i F) = _ from ih hf (H.drop i), map_smul]
    push_cast
    module

end derivation

end YM.WilsonMS
