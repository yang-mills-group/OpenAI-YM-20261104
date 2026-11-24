import YM.WilsonMS.Top.Position

/-! # Matrices of the finite Fourier transform. No mode omitted yet. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.FFT
open Function Finset Matrix Complex Lattice Bloch MS.Orbit
open scoped BigOperators ComplexConjugate

variable (I : Type) [DecidableEq I] (n : Side)

abbrev delta (i j : I) : ℂ :=
  if i = j then 1 else 0

def forward : Matrix (I × Site n) (I × Site n) ℂ := fun x p => if x.1 = p.1 then cell x.2 p.2 else 0

def backward : Matrix (I × Site n) (I × Site n) ℂ := fun x p =>
  if x.1 = p.1 then scaleZ n * (cell x.2 p.2)⁻¹ else 0

def rev : Matrix (I × Site n) (I × Site n) ℂ := fun i j => if i = (j.1, -j.2) then 1 else 0

def exclude0 : Matrix (I × Site n) (I × Site n) ℂ := fun i j =>
  if i.2 = 0 then 0 else (1 : Matrix _ _ ℂ) i j

variable [Fintype I]
local notation "F'" => forward I n
local notation "R'" => rev I n
local notation "B'" => backward I n

lemma backward_inverse : B' * F' = 1 := by
  classical
  ext ⟨i, x⟩ ⟨j, y⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  conv_lhs => arg 2; ext a; arg 2; ext s; dsimp only [forward, backward]
  rw [Finset.sum_eq_single_of_mem i (mem_univ _)]
  swap
  · intro k _ hk
    simp [Ne.symm hk]
  by_cases he : i = j
  swap
  · simp [he]
  subst j
  simp only [ite_true]
  rw [show (∑ k : Site n, _) = scaleZ n * ∑ k : Site n, cell y k * (cell x k)⁻¹ from ?_]
  swap
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [cell_duality k y]
    ring
  rw [Bloch.orthogonal, ← Position.volumeFactor, Matrix.one_apply]
  by_cases hx : x = y
  · subst y
    simp only [ite_true]
    exact lightW n
  simp [Ne.symm hx, hx]

lemma forward_inverse : F' * B' = 1 :=
  mul_eq_one_comm.mp (backward_inverse ..)

omit [Fintype I] in
lemma symmetric : F'ᵀ = F' := by
  ext i j
  rw [transpose_apply]
  unfold forward
  split_ifs with h g g
  exact cell_duality _ _
  exact (g h.symm).elim
  exact (h g.symm).elim
  rfl

lemma gram : F'ᵀ * F' = brightness n • R' := by
  classical
  ext ⟨i, x⟩ ⟨j, y⟩
  rw [symmetric I n, Matrix.mul_apply, Fintype.sum_prod_type]
  unfold forward
  rw [Finset.sum_eq_single_of_mem i (mem_univ _)]
  swap
  · intro k _ hk
    simp [Ne.symm hk]
  rw [Matrix.smul_apply]
  unfold rev
  dsimp only
  by_cases he : i = j
  swap
  · simp [he]
  subst j
  simp_rw [ite_true]
  have ht : ∑ k : Site n, cell x k * cell k y = ∑ k : Site n, cell x k * (cell (-y) k)⁻¹ := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [cell_duality (-y), cell_inverse, inv_inv]
  rw [ht, Bloch.orthogonal]
  by_cases he : x = -y <;> simp [he, Position.volumeFactor]

variable {I n}
section flipM
variable {A : Type}

lemma rev_mul (C : Matrix (I × Site n) A ℂ) (u : I × Site n) (j : A) :
    (R' * C) u j = C (u.1, -u.2) j := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem (u.1, -u.2) (mem_univ _), show R' u _ = 1 from ?_,
    one_mul]
  unfold rev
  rw [if_pos]
  simp
  rintro ⟨k, p⟩ _ hp
  rw [show R' u (k, p) = 0 from if_neg (show ¬u = (k, -p) from fun h => hp (by simp [h])), zero_mul]

lemma mul_rev (C : Matrix A (I × Site n) ℂ) (u : A) (j : I × Site n) :
    (C * R') u j = C u (j.1, -j.2) := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem (j.1, -j.2) (mem_univ _),
    show R' _ _ = 1 from if_pos rfl, mul_one]
  intro a _ he
  rw [show R' _ _ = 0 from if_neg he, mul_zero]
end flipM
variable (I n)

lemma inverse_by_rev : B' = scaleZ n • (R' * F'ᵀ) := by
  ext ⟨i, x⟩ ⟨j, y⟩
  rw [Matrix.smul_apply, rev_mul, symmetric I n]
  unfold backward forward
  dsimp only
  split_ifs
  rw [cell_duality (-x), cell_inverse, cell_duality x]
  rfl
  rw [smul_zero]

variable {I n}

def originP (I : Type) (n : Side) [DecidableEq I] [Fintype I] : Matrix (I × Site n) (I × Site n) ℂ :=
  forward I n * (1 - exclude0 I n) * backward I n

lemma origin_cell (i j : I) (x y : Site n) :
    originP I n (i, x) (j, y) = if i = j then scaleZ n else 0 := by
  classical
  let H := 1 - exclude0 I n
  have h (t k : I × Site n) : H t k = if t = k ∧ t.2 = 0 then 1 else 0 := by
    unfold H exclude0
    rw [Matrix.sub_apply]
    by_cases he : t.2 = 0 <;> simp [he, one_apply]
  have ht k p : (F' * H) (i, x) (k, p) = if k = i ∧ p = 0 then 1 else 0 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem (k, p) (mem_univ _), h]
    by_cases hx : p = 0
    subst p
    simp [forward, eq_comm]
    simp [hx]
    intro j _ hj
    rw [h, if_neg (fun v => hj v.1), mul_zero]
  change (F' * H * B') _ _ = _
  rw [Matrix.mul_apply, sum_eq_single_of_mem (i, 0) (mem_univ _), ht]
  simp [backward, cell_duality (0 : Site n)]
  rintro ⟨f, u⟩ _ hv
  rw [ht, if_neg (fun h => hv (Prod.ext h.1 h.2)), zero_mul]

end YM.WilsonMS.FFT
