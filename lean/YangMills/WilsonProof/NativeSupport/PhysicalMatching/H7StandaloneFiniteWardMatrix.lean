import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
open scoped BigOperators
namespace PhysicalMatching.H7StandaloneFiniteWardMatrix

abbrev Coords := Fin 4 → ℂ
abbrev Matrix4 := Matrix (Fin 4) (Fin 4) ℂ

def size (u : Coords) : ℝ := ∑ i, ‖u i‖
def matrixSize (A : Matrix4) : ℝ := ∑ i, ∑ k, ‖A i k‖
def act (A : Matrix4) (u : Coords) : Coords := fun i => ∑ k, A i k * u k

theorem size_nonneg (u : Coords) : 0 ≤ size u :=
  Finset.sum_nonneg fun i _ => norm_nonneg (u i)

theorem matrixSize_nonneg (A : Matrix4) : 0 ≤ matrixSize A :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => norm_nonneg (A i k)

theorem coordinate_le (u : Coords) (i : Fin 4) : ‖u i‖ ≤ size u :=
  Finset.single_le_sum (fun k _ => norm_nonneg (u k)) (Finset.mem_univ i)

theorem size_add (u v : Coords) : size (u+v) ≤ size u + size v := by
  unfold size
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => norm_add_le (u i) (v i)

theorem actPrice (A : Matrix4) (u : Coords) : size (act A u) ≤ matrixSize A * size u := by
  calc
    _ ≤ ∑ i : Fin 4, ∑ k : Fin 4, ‖A i k * u k‖ :=
      Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i : Fin 4, ∑ k : Fin 4, ‖A i k‖ * size u := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (coordinate_le u k) (norm_nonneg _)
    _ = _ := by simp only [matrixSize,Finset.sum_mul]

theorem actAdd (A : Matrix4) (u v : Coords) : act A (u+v) = act A u + act A v := by
  funext i
  simp [act,mul_add,Finset.sum_add_distrib]

theorem actSub (A : Matrix4) (u v : Coords) : act A (u-v) = act A u - act A v := by
  funext i
  simp [act,mul_sub,Finset.sum_sub_distrib]

theorem subAct (A L : Matrix4) (u : Coords) : act (L-A) u = act L u - act A u := by
  funext i
  simp [act,sub_mul,Finset.sum_sub_distrib]

theorem fitted (B L A : Matrix4) (ground : ∀ u, act B (act L u) = u)
    (small : matrixSize B * matrixSize (L-A) ≤ 1/2) (u f b : Coords) :
    size (u-f) ≤ 2 * matrixSize B * (size (act A u - b) + size (b - act A f)) := by
  let x := u-f
  have split : x = act B (act A x) + act B (act (L-A) x) := by
    rw [← actAdd,subAct]
    have eq : act A x + (act L x - act A x) = act L x := by abel
    rw [eq,ground]
  have rhs : act A x = (act A u-b) + (b-act A f) := by
    dsimp [x]
    rw [actSub]
    abel
  have h₁ : size (act B (act A x)) ≤ matrixSize B * (size (act A u-b)+size (b-act A f)) :=
    (actPrice B _).trans (mul_le_mul_of_nonneg_left (rhs ▸ size_add _ _) (matrixSize_nonneg _))
  have h₂ : size (act B (act (L-A) x)) ≤ (matrixSize B * matrixSize (L-A)) * size x := by
    calc
      _ ≤ matrixSize B * size (act (L-A) x) := actPrice B _
      _ ≤ matrixSize B * (matrixSize (L-A) * size x) :=
        mul_le_mul_of_nonneg_left (actPrice (L-A) x) (matrixSize_nonneg _)
      _ = _ := (mul_assoc _ _ _).symm
  have key : size x ≤ matrixSize B * (size (act A u-b)+size (b-act A f)) + (1/2)*size x := by
    calc
      size x = size (act B (act A x) + act B (act (L-A) x)) := congrArg size split
      _ ≤ _ := (size_add _ _).trans (add_le_add h₁ (h₂.trans (mul_le_mul_of_nonneg_right small (size_nonneg x))))
  change size x ≤ _
  linarith

def coefficients (B : Matrix4) (L : ℕ → Matrix4) (b : ℕ → Coords) (n : ℕ) : Coords :=
  Nat.strongRecOn n fun m earlier => act B (b m - ∑ k : Fin m,
    act (L (k.val+1)) (earlier (m-(k.val+1)) (by omega)))

theorem coefficients_eq (B : Matrix4) (L : ℕ → Matrix4) (b : ℕ → Coords) (n : ℕ) :
    coefficients B L b n = act B (b n - ∑ k : Fin n,
      act (L (k.val+1)) (coefficients B L b (n-(k.val+1)))) := by
  unfold coefficients
  rw [Nat.strongRecOn_eq]

theorem groundCoefficient (B : Matrix4) (L : ℕ → Matrix4) (b : ℕ → Coords) :
    coefficients B L b 0 = act B (b 0) := by
  rw [coefficients_eq]
  simp

theorem coefficientBalance (B : Matrix4) (L : ℕ → Matrix4) (b : ℕ → Coords)
    (ground : ∀ x, act (L 0) (act B x) = x) (n : ℕ) :
    act (L 0) (coefficients B L b n) +
      ∑ k : Fin n, act (L (k.val+1)) (coefficients B L b (n-(k.val+1))) = b n := by
  rw [coefficients_eq B L b n,ground]
  abel

end PhysicalMatching.H7StandaloneFiniteWardMatrix

