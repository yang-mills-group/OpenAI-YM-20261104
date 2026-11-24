import YM.MS.Swirl.Cut

/-!
# Linear vector fields on a finite MS alphabet

In particular a pair of odd fields contracting on **letters** gives a free Koszul
resolution on the finite-rank graded-symmetric tensors. This will be used with based gauge
letters; the mean-zero prescription including residual constant ghost modes is *not*
acyclic.
-/

set_option autoImplicit false
noncomputable section

namespace YM.WilsonBridge
open MS MS.Koszul MS.Swirl MS.Puff MS.Cylinder
open MS.Orbit
open Function Finset
open scoped BigOperators
variable {V : Type} {p : Sector V} {F G : Raw V ℂ}

lemma rank_limit {n : ℤ} (h : Book.rank n F) : Book.Limit F n :=
  fun l hl => h l (by rw [Book.mod_int]; omega)
lemma rank_zero_eq_coin (h : Book.rank 0 F) : F = coin (F []) := by
  funext l
  cases l with
  | nil => rfl
  | cons x l => exact h _ (by rw [Book.mod_int]; simp; omega)
lemma limit_zero_eq_coin (h : Book.Limit F 0) : F = coin (F []) := by
  funext l
  cases l with
  | nil => rfl
  | cons x l => exact h _ (by simp)
lemma rank_letter (i : V) : Book.rank 1 (atLetter i (R := ℂ)) :=
  Rails.letter (v := fun _ => 1) i
lemma mask_symm {d : ℤ} (hs : MS.Koszul.Symm p F) : MS.Koszul.Symm p (Book.mask d F) := by
  intro a i j l
  by_cases h : ((a ++ i :: j :: l).length : ℤ) = d
  · rw [Book.enough _ h, Book.enough _ (by simpa using h)]
    exact hs a i j l
  rw [Book.strange _ h, Book.strange _ (by simpa using h), mul_zero]
lemma mask_pure {d : ℤ} {b : Bool} (hs : Pure p b F) : Pure p b (Book.mask d F) := by
  intro l hl
  by_cases h : (l.length : ℤ) = d
  · exact (Book.enough _ h).trans (hs l hl)
  exact Book.strange _ h
lemma limit_mask_off {d e : ℤ} (h : Book.Limit F d) (hde : d < e) : Book.mask e F = 0 := by
  funext l
  by_cases hu : (l.length : ℤ)=e
  · exact (Book.enough l hu).trans (h l (by omega))
  exact Book.strange l hu
lemma limit_eq_rankSum (n : ℕ) (h : Book.Limit F n) :
    F = ∑ k ∈ range (n+1), Book.mask k F := by
  funext l
  rw [Finset.sum_apply]
  by_cases hh : l.length ≤ n
  · rw [sum_eq_single_of_mem l.length (mem_range.mpr (by omega))
      (fun b _ hb => Book.strange _ (by omega))]
    exact (Book.enough _ rfl).symm
  rw [Finset.sum_eq_zero (fun x (he:x ∈ range (n+1)) =>
    Book.strange _ (by have h' := mem_range.mp he; omega))]
  exact h _ (by omega)
lemma limit_down {d : ℤ} (h : Book.Limit F d) (hh : Book.mask d F = 0) :
    Book.Limit F (d-1) := by
  intro l hl
  by_cases he : (l.length : ℤ) = d
  · exact (Book.enough _ he).symm.trans (congr_fun hh l)
  exact h _ (by omega)
lemma tick_rank (n : ℕ) (h : Book.rank n F) : Tick (fun _ => 1) F = (n:ℂ) • F := by
  funext l
  change ((l.map (fun _ => (1:ℂ))).sum * _) = (n:ℂ)* F l
  by_cases hl : l.length=n
  · rw [List.map_const',List.sum_replicate,hl]; simp
  rw [h _ (by rw [Book.mod_int]; omega)]; simp

variable [Fintype V]

lemma expand_rank (n : ℕ) (hn : 0 < n) (h : Book.rank n F) (hF : MS.Koszul.Symm p F) :
    F = (n:ℂ)⁻¹ • ∑ x : V, product p (atLetter x) (D x F) := by
  have H := overture (fun _ : V => 1) hF
  rw [tick_rank n h] at H
  simp only [one_smul] at H
  rw [← H, inv_smul_smul₀ (by exact_mod_cast Nat.ne_of_gt hn)]

/-- In the column convention: `field x` is the value of the derivation on `x`. -/
structure OddField (p : Sector V) where
  field : V → Raw V ℂ
  rank (x) : Book.rank 1 (field x)
  odd (x) : Pure p (!(p x)) (field x)
  symm (x) : MS.Koszul.Symm p (field x)

namespace OddField
variable (X Y : OddField p)
local infixl:70 " ⋆ " => product p

def deriv : Op V ℂ := ∑ x : V, (product p (X.field x)).comp (D x)
lemma run (F) : X.deriv F = ∑ x, X.field x ⋆ D x F := by
  simp [deriv,LinearMap.sum_apply]
lemma on_letter (x : V) : X.deriv (atLetter x)=X.field x := by
  classical
  rw [X.run, Finset.sum_eq_single_of_mem x (mem_univ _), hear]
  · rw [← Pure.central (v := X.field x) (coin_pure 1), coin_product, one_smul]
  intro i _ hi
  rw [unheard x hi,map_zero]
lemma on_coin (c : ℂ) : X.deriv (coin c)=0 := by rw [X.run]; simp [coin_nod]
lemma apply_rank {n : ℤ} (h : Book.rank n F) : Book.rank n (X.deriv F) := by
  rw [X.run]; refine Rails.sum _ (fun i _=>?_)
  have hh := (X.rank i).product (p:=p) (h.enter i)
  simpa using hh
lemma apply_symm (h : MS.Koszul.Symm p F) : MS.Koszul.Symm p (X.deriv F) := by
  rw [X.run]; exact Symm.sum _ (fun i _ => (X.symm i).times (h.drop i))
lemma apply_pure {b : Bool} (h : Pure p b F) : Pure p (!b) (X.deriv F) := by
  rw [X.run]; refine Pure.sum _ (fun i _=>?_)
  have hh := (X.odd i).prod (h.drop i)
  rcases b with _|_ <;> cases hi : p i <;> simpa [hi] using hh
lemma product_rule {b : Bool} (h : Pure p b F) :
    X.deriv (F ⋆ G) = X.deriv F ⋆ G + (cross true b:ℂ) • (F ⋆ X.deriv G) := by
  simp_rw [X.run, map_sum, LinearMap.sum_apply,Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [D_product,h.signs,map_add,map_smul,LinearMap.smul_apply,map_smul, ← times_assoc,
    ← times_assoc (X.field i) F, (X.odd i).times_comm h,map_smul,LinearMap.smul_apply,
    smul_smul, times_assoc]
  rw [← cross_left]; cases hi:p i <;> simp [times_assoc]

-- Contract on rank n columns using only the letter relations

def bracket : Op V ℂ := X.deriv.comp Y.deriv + Y.deriv.comp X.deriv
lemma bracket_apply : bracket X Y F = X.deriv (Y.deriv F) + Y.deriv (X.deriv F) := rfl
lemma bracket_letter {x : V} (h : X.deriv (Y.field x)+Y.deriv (X.field x)=atLetter x) :
    bracket X Y (atLetter x)=atLetter x := by rw [bracket_apply,Y.on_letter,X.on_letter,h]
lemma bracket_product {b : Bool} (h : Pure p b F) :
    bracket X Y (F ⋆ G) = bracket X Y F ⋆ G + F ⋆ bracket X Y G := by
  simp only [bracket_apply, X.product_rule h,Y.product_rule h,map_add,map_smul]
  rw [X.product_rule (Y.apply_pure h), Y.product_rule (X.apply_pure h)]
  simp only [LinearMap.add_apply]; cases b <;> simp <;> abel

lemma bracket_rank (H : ∀ x, X.deriv (Y.field x)+Y.deriv (X.field x)=atLetter x)
    (n : ℕ) (h : Book.rank n F) (hF : MS.Koszul.Symm p F) : bracket X Y F = (n:ℂ) • F := by
  induction n generalizing F with
  | zero =>
    push_cast at *
    rw [zero_smul, rank_zero_eq_coin h, bracket_apply, X.on_coin, Y.on_coin, map_zero, map_zero, add_zero]
  | succ n ih =>
    have he (x:V) : bracket X Y (atLetter x ⋆ D x F) = (↑(n+1:ℕ):ℂ) • (atLetter x ⋆ D x F) := by
      have hu : Book.rank n (D x F) := by simpa using h.enter x
      rw [X.bracket_product _ (speaks_p x),X.bracket_letter Y (H x),ih hu (hF.drop _),map_smul]
      push_cast; module
    have hE := expand_rank (n+1) (by omega) h hF
    calc
      _ = bracket X Y ((↑(n+1:ℕ):ℂ)⁻¹ • ∑ x : V, (atLetter x ⋆ D x F)) := congr_arg _ hE
      _ = (↑(n+1:ℕ):ℂ) • ((↑(n+1:ℕ):ℂ)⁻¹ • ∑ x : V, (atLetter x ⋆ D x F)) := by rw [map_smul,map_sum]; simp_rw [he,← Finset.smul_sum]; exact smul_comm ..
      _ = _ := congr_arg ((↑(n+1:ℕ):ℂ) • ·) hE.symm
end OddField

end YM.WilsonBridge
