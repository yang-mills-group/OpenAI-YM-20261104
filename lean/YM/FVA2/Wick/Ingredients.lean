import YM.FVA2.Slice.Triad
/-! # Supercoordinates for the joint boson / FP Wick calculation

Only linear-jet algebra in this file. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick
open Function Set Finset
open MS MS.Koszul MS.Cylinder MS.Plane MS.Orbit MS.Cylinder.Taylor
open scoped BigOperators Matrix Topology ContDiff
variable {A J : Type} {E : Type}

section pulls
variable (D : Type) [Fintype D]
variable (j : D)
lemma letter_pull [Fintype A] (L : Matrix D A ℂ) :
    pull L (atLetter j) = ∑ k : A, L j k • atLetter k := by
  classical
  apply ext_D
  · simp only [pull_nil, Finset.sum_apply, Pi.smul_apply]; simp [atLetter]
  intro i; rw [map_sum]
  simp_rw [map_smul]
  rw [Finset.sum_eq_single i]; swap
  · intro k _ h; rw [unheard k (Ne.symm h), smul_zero]
  swap; · exact fun h=> (h (Finset.mem_univ _)).elim
  change MS.Koszul.D i (pull L (Cylinder.single j).val) = _
  rw [pull_shade,names, hear, Matrix.transpose_apply]
lemma matrix_pair (L : Matrix D A ℂ) (F : Raw D ℂ) (i j : A) :
    pull L F [i,j] = (Lᵀ * Matrix.of (fun i j : D => F [i,j]) * L) i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    pull, lantern, Cylinder.lit,LinearMap.coe_mk,AddHom.coe_mk, Finset.mul_sum, at_D, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring
end pulls

section bosons
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- The vector entries of a coordinate assignment that are actually commuting. -/
def eased (e : A → E) : Index A J → E := Sum.elim e (fun _ => 0)
omit [NormedSpace ℝ E] in
lemma eased_p (e : A → E) (i : Index A J) (h : sector i=true) : eased e i=0 := by
  rcases i with i|j; cases h; rfl
abbrev Inks (e : A→E) (f : E→ℝ) : Raw (Index A J) ℂ := ink (eased e) f
end bosons

/-- The ordered pair `bar_i c_j`, with left-derivative convention on raw bills. -/
def xy (i j : J) : Raw (Index A J) ℂ := product sector (atLetter (bar i)) (atLetter (ghost j))
local notation "b" => sector (A:=A) (J:=J)
local infixl:70 " ⋆ " => product b
lemma xy_p (i j : J) : Pure b false (xy i j) := (speaks_p (p:=b) (bar i)).prod (speaks_p (ghost j))
lemma xy_s (i j : J) : Symm b (xy i j) := (speaks_s _).times (speaks_s _)
variable [DecidableEq J]
omit [DecidableEq J] in
lemma xy_deg (i j : J) : Book.rank 2 (xy (A:=A) i j) := (Rails.letter _).product (Rails.letter _) -- scope
end YM.FVA2.Wick
