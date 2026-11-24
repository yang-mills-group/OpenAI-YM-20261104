import YM.MS.Swirl.Came
import YangMills.WilsonProof.NativeSupport.YM.MS.Cylinder.Variable
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Pull-back of the MS finite Wick operation under linear coordinates

Bills in `Raw` are lists of left-derivative coefficients at zero (anticommuting signs where
needed). Matrices in this bridge act on **field vectors**, not on the arguments of `shade`:
old field = L • new field. Thus the argument to `lantern` is Lᵀ. Later we'll pull back the
MS Fourier bills to position-space, then to divergence-free real links and pairs of root
(finite ghost) variables. We retain momentum phases and use transposes, not adjoints, on these
complexifications.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick
open Function Set Finset
open MS MS.Koszul MS.Plane MS.Cylinder MS.Book MS.Orbit MS.Orbit.Cog MS.Swirl
open scoped BigOperators Matrix
variable {A B C : Type}

section matrix
variable [Fintype A] (L : Matrix A B ℂ) {p : Sector A} {q : Sector B}

/-- Literal substitution of a matrix into formal Grassmann and point variables. -/
def pull : Raw A ℂ →ₗ[ℂ] Raw B ℂ := lantern Finset.univ Lᵀ

theorem pull_nil (F : Raw A ℂ) : pull L F [] = F [] := rfl

theorem pull_D (b : B) (F : Raw A ℂ) :
    D b (pull L F) = ∑ i, (L i b) • pull L (D i F) := lantern_drop ..

theorem pull_shade (F : Cyl A ℂ) : pull L F.val = shade Lᵀ F :=
  (tinted _ F (show Uses ((Finset.univ : Finset A) : Set A) F.val from by
    simpa only [Finset.coe_univ] using Uses.entire F.val)).symm

theorem pull_limit {F : Raw A ℂ} {h : ℤ} (H : Limit F h) : Limit (pull L F) h := by
  let f : Cyl A ℂ := ⟨F, all_f F⟩
  change Limit (pull L f.val) _
  rw [pull_shade]
  exact Limit.shades _ H _

theorem pull_mask (h : ℤ) (F : Raw A ℂ) : pull L (Book.mask h F) = mask h (pull L F) := by
  let f : Cyl A ℂ := ⟨F, all_f F⟩
  change pull L (model h f).val = mask h (pull L f.val)
  rw [pull_shade, pull_shade, mod_ink]

theorem pull_symm {L : Matrix A B ℂ} (ht : Tie p q Lᵀ) {F : Raw A ℂ}
    (H : Symm p F) : Symm q (pull L F) := by
  let f : Cyl A ℂ := ⟨F, all_f F⟩
  rw [pull_shade L f]
  exact ht.sym f H

theorem pull_pure {L : Matrix A B ℂ} (ht : Tie p q Lᵀ) {b : Bool} {F : Raw A ℂ}
    (H : Pure p b F) : Pure q b (pull L F) := by
  let f : Cyl A ℂ := ⟨F, all_f F⟩
  rw [pull_shade L f]
  exact ht.pure f H

theorem pull_product {L : Matrix A B ℂ} (ht : Tie p q Lᵀ) (F H : Raw A ℂ) :
    pull L (product p F H) = product q (pull L F) (pull L H) := by
  let f : Cyl A ℂ := ⟨F, all_f F⟩
  let h : Cyl A ℂ := ⟨H, all_f H⟩
  change pull L (couple p f h).val = product q (pull L f.val) (pull L h.val)
  rw [pull_shade, pull_shade, pull_shade, ht.prod f h]

theorem pull_coin (z : ℂ) : pull L (coin z) = coin z := by
  change pull L (piece z).val = _
  rw [pull_shade L (piece z)]
  exact coin_turn ..

theorem pull_one [DecidableEq A] (F : Raw A ℂ) : pull (1 : Matrix A A ℂ) F = F := by
  funext l; induction l generalizing F with
  | nil => rfl
  | cons a l ih =>
    rw [D_eval a (pull _ _), pull_D, Finset.sum_eq_single a]
    · simp only [Matrix.one_apply, if_true, one_smul, ih, at_D]
    · intro b _ h; simp [h]
    simp

/-- `A` and `B` are the old and intermediate coordinates, respectively. -/
theorem pull_comp [Fintype B] (M : Matrix B C ℂ) (F : Raw A ℂ) :
    pull M (pull L F) = pull (L * M) F := by
  funext l; induction l generalizing F with
  | nil => rfl
  | cons b l ih =>
    rw [D_eval b (pull M _), pull_D, D_eval b (pull (L*M) _), pull_D]
    simp only [Finset.sum_apply, Pi.smul_apply, pull_D, map_sum, map_smul, ih,
      Matrix.mul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

omit [Fintype A] in
theorem tie_comp {c : Sector C} (ht : Tie p q Lᵀ) [Fintype B] (M : Matrix B C ℂ)
    (hm : Tie q c Mᵀ) : Tie p c ((L * M)ᵀ) := by
  intro i j h
  by_contra he
  apply h
  apply Finset.sum_eq_zero
  intro k _
  by_contra hk
  exact he ((ht i k (left_ne_zero_of_mul hk)).trans (hm k j (right_ne_zero_of_mul hk)))

-- covariance
variable [Fintype B]

/-- `frame` commutes with pull-back, turning the covariance into `L K Lᵀ`. The Grains are
*half* the covariance. The order `[i,j]` of derivatives is preserved on the nose. -/
theorem pull_frame (K : Matrix B B ℂ) (F : Raw A ℂ) :
    frame K (pull L F) = pull L (frame (L * K * Lᵀ) F) := by
  simp only [fpΩ, diffPair_apply, pull_D, map_sum, map_smul, Finset.smul_sum,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_smul, Finset.sum_mul]
  -- Order at LHS (b1 b2 a1 a2), RHS (a1 a2 b2 b1)
  conv_lhs =>
    arg 2; intro x
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs =>
    arg 2; intro x
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul, smul_smul, mul_comm (K b a)]

theorem pull_tep (K : Matrix B B ℂ) (F : Raw A ℂ) (n : ℕ) :
    tep K n (pull L F) = pull L (tep (L * K * Lᵀ) n F) := by
  induction n with
  | zero => rw [rise, rise]; rfl
  | succ n ih => rw [teen, teen, ih, pull_frame, map_smul]

/-- Linearity in the external fields, with no injectivity or nondegeneracy premise. -/
theorem pull_Wick (K : Matrix B B ℂ) (F : Raw A ℂ) (h : F ∈ Mini A) :
    View K (pull L F) = View (L * K * Lᵀ) F := by
  obtain ⟨n, hn⟩ := h
  change Shot _ _ [] = Shot _ _ []
  rw [dawn K (pull_limit L hn), dawn _ hn]
  simp only [effect, LinearMap.sum_apply, Finset.sum_apply, pull_tep, pull_nil]

end matrix
end YM.FVA2.Wick
