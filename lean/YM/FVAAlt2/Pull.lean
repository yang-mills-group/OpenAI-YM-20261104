import YangMills.WilsonProof.NativeSupport.YM.MS.Book.Mask

/-!
# Finite matrix interface for field and gauge changes in the MS coefficient calculation

Preserves the **native** MS kernel convention (kernel indexed by a list of slots,
no Taylor factorial on differentiating, Grassmann parities, arity restrictions).
Used for both the finite Fourier transform and pullback to the actual Landau
and ghost integration variables. Matrix convention: the FIRST index is the
new variable, old field y expressed as (ordinary) transpose times new field.
In particular even for complex R we will not implicitly conjugate Fourier modes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open Finset MS MS.Koszul MS.Book MS.Cylinder
variable {X Y Z R : Type} [Fintype X] [CommRing R]

abbrev pull (L : Matrix Y X R) : Raw X R →ₗ[R] Raw Y R := lantern univ L

variable (L : Matrix Y X R) {p : Sector X} {q : Sector Y}

lemma eq_pull (f : Cyl X R) : shade L f = pull L f.val :=
  tinted L f (by rw [coe_univ]; exact Uses.entire _)

@[simp] lemma pull_nil (f : Raw X R) : pull L f [] = f [] := rfl

lemma pull_D (f : Raw X R) (y : Y) : D y (pull L f) = ∑ x, L y x • pull L (D x f) :=
  lantern_drop ..

lemma pull_cons (f : Raw X R) (y : Y) (l : List Y) :
    pull L f (y :: l) = ∑ x, L y x * pull L (D x f) l := by
  rw [D_eval y (pull L f), pull_D, Finset.sum_apply]; rfl

lemma pull_two (f : Raw X R) (i j : Y) : pull L f [i,j] = ∑ x, ∑ y, L i x * f [x,y] * L j y := by
  rw [pull_cons]
  simp_rw [pull_cons, Finset.mul_sum, pull_nil, at_D]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  ring

def pairMatrix (f : Raw X R) : Matrix X X R := fun x y => f [x,y]

lemma pull_pairMatrix [Fintype Y] (f : Raw X R) :
    pairMatrix (pull L f) = L * pairMatrix f * L.transpose := by
  ext i j
  simp_rw [Matrix.mul_apply, Finset.sum_mul, pairMatrix, pull_two]; exact Finset.sum_comm

lemma pull_mask (f : Raw X R) (v : ℤ) : pull L (mask v f) = mask v (pull L f) := by
  have h := mod_ink (h:=v) (region.symm f) L
  rw [eq_pull, eq_pull] at h
  exact h

lemma pull_limit {v : ℤ} {f : Raw X R} (h : Limit f v) : Limit (pull L f) v := by
  have hm := Limit.shades (region.symm f) h L
  rw [eq_pull] at hm
  exact hm

lemma pull_coin (r : R) : pull L (coin r) = coin r := by
  refine ext_D rfl ?_
  intro i
  have hD {S : Type} (j : S) : D j (coin r) = 0 := rfl -- funext?
  rw [pull_D]; simp_rw [hD,map_zero,smul_zero,sum_const_zero]

lemma pull_atLetter (x : X) (y : Y) : pull L (atLetter x) [y] = L y x := by
  classical
  rw [pull_cons, Finset.sum_eq_single x]
  · simp only [hear, pull_nil]; exact mul_one _
  · intro j _ hj; simp [unheard x hj]
  simp

variable {L}
lemma pull_product (h : Tie p q L) (f g : Raw X R) :
    pull L (product p f g) = product q (pull L f) (pull L g) := by
  have hm := h.prod (region.symm f) (region.symm g)
  rw [eq_pull, eq_pull, eq_pull] at hm
  exact hm

lemma pull_symm (h : Tie p q L) {f : Raw X R} (hf : Symm p f) : Symm q (pull L f) := by
  have hm := h.sym (region.symm f) hf
  rw [eq_pull] at hm
  exact hm

lemma pull_pure (h : Tie p q L) {f : Raw X R} {b : Bool} (hf : Pure p b f) : Pure q b (pull L f) := by
  have hm := h.pure (region.symm f) hf
  rw [eq_pull] at hm
  exact hm
end YM.FVAAlt2
