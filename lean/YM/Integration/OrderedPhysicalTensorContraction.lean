import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Prod

/-!
# Physical-slot contraction of an ordered tensor

The supplied equivalence records the original slot order. Physical slots are
summed against the same fixed real vector; no symmetrization or normalization
change occurs. A fixed free port retains its marginal bound. If a physical port
exists, its vector weight supplies the anchor for the whole remaining sum.
-/

set_option autoImplicit false

open scoped BigOperators

namespace YM.Integration.OrderedPhysicalTensorContraction

noncomputable section

/-- Reconstruct the original ordered assignment from its two groups of slots. -/
def assemble {n : ℕ} {F P I : Type*} (e : Fin n ≃ F ⊕ P)
    (x : F → I) (y : P → I) : Fin n → I :=
  fun k => Sum.elim x y (e k)

/-- Contract only physical slots of the original table against the fixed vector. -/
def contract {n : ℕ} {F P I : Type*} [Fintype P] [DecidableEq P] [Fintype I]
    (e : Fin n ≃ F ⊕ P) (T : (Fin n → I) → ℂ) (v : I → ℝ)
    (x : F → I) : ℂ :=
  ∑ y : P → I, T (assemble e x y) * ∏ p : P, (v (y p) : ℂ)

private theorem assemble_free {n : ℕ} {F P I : Type*} (e : Fin n ≃ F ⊕ P)
    (x : F → I) (y : P → I) (f : F) :
    assemble e x y (e.symm (Sum.inl f)) = x f := by
  simp [assemble]

private theorem assemble_physical {n : ℕ} {F P I : Type*} (e : Fin n ≃ F ⊕ P)
    (x : F → I) (y : P → I) (p : P) :
    assemble e x y (e.symm (Sum.inr p)) = y p := by
  simp [assemble]

private def assignmentEquiv {n : ℕ} {F P I : Type*} (e : Fin n ≃ F ⊕ P) :
    ((F → I) × (P → I)) ≃ (Fin n → I) :=
  (Equiv.sumArrowEquivProdArrow F P I).symm.trans
    (Equiv.arrowCongr e (Equiv.refl I)).symm

private theorem sum_assemble {n : ℕ} {F P I : Type*}
    [Fintype F] [DecidableEq F] [Fintype P] [DecidableEq P] [Fintype I]
    (e : Fin n ≃ F ⊕ P) (g : (Fin n → I) → ℝ) :
    (∑ x : F → I, ∑ y : P → I, g (assemble e x y)) = ∑ z : Fin n → I, g z := by
  have h := (assignmentEquiv (I := I) e).sum_comp g
  change (∑ p : (F → I) × (P → I), g (assemble e p.1 p.2)) =
    ∑ z : Fin n → I, g z at h
  rw [← Finset.univ_product_univ, Finset.sum_product] at h
  exact h

private theorem vector_point_le {I : Type*} [Fintype I]
    (v : I → ℝ) (D : ℝ) (hv : (∑ i, |v i|) ≤ D) (i : I) : |v i| ≤ D :=
  (Finset.single_le_sum (f := fun j => |v j|)
    (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)).trans hv

private theorem vector_product_le {P I : Type*}
    (v : I → ℝ) (D : ℝ) (hp : ∀ i, |v i| ≤ D)
    (s : Finset P) (y : P → I) :
    (∏ p ∈ s, |v (y p)|) ≤ D ^ s.card := by
  have h : (∏ p ∈ s, |v (y p)|) ≤ ∏ _p ∈ s, D :=
    Finset.prod_le_prod (fun p _ => abs_nonneg (v (y p))) (fun p _ => hp (y p))
  simpa only [Finset.prod_const] using h

private theorem weighted_fiber_le {X I : Type*} [Fintype X]
    [Fintype I] [DecidableEq I]
    (T : X → ℂ) (observe : X → I) (v : I → ℝ) (A D : ℝ)
    (hA : 0 ≤ A)
    (hT : ∀ i, (∑ z : X, if observe z = i then ‖T z‖ else 0) ≤ A)
    (hv : (∑ i, |v i|) ≤ D) :
    (∑ z : X, ‖T z‖ * |v (observe z)|) ≤ A * D := by
  calc
    (∑ z : X, ‖T z‖ * |v (observe z)|) =
        ∑ z : X, ∑ i : I, (if observe z = i then ‖T z‖ else 0) * |v i| := by
      apply Finset.sum_congr rfl
      intro z _hz
      simp [ite_mul]
    _ = ∑ i : I, ∑ z : X, (if observe z = i then ‖T z‖ else 0) * |v i| :=
      Finset.sum_comm
    _ = ∑ i : I, (∑ z : X, if observe z = i then ‖T z‖ else 0) * |v i| := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_mul]
    _ ≤ ∑ i : I, A * |v i| :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hT i) (abs_nonneg _))
    _ = A * ∑ i : I, |v i| := by rw [Finset.mul_sum]
    _ ≤ A * D := mul_le_mul_of_nonneg_left hv hA

private theorem norm_contract_le {n : ℕ} {F P I : Type*}
    [Fintype P] [DecidableEq P] [Fintype I]
    (e : Fin n ≃ F ⊕ P) (T : (Fin n → I) → ℂ) (v : I → ℝ) (x : F → I) :
    ‖contract e T v x‖ ≤
      ∑ y : P → I, ‖T (assemble e x y)‖ * ∏ p : P, |v (y p)| := by
  unfold contract
  calc
    ‖∑ y : P → I, T (assemble e x y) * ∏ p : P, (v (y p) : ℂ)‖ ≤
        ∑ y : P → I, ‖T (assemble e x y) * ∏ p : P, (v (y p) : ℂ)‖ :=
      norm_sum_le _ _
    _ = ∑ y : P → I, ‖T (assemble e x y)‖ * ∏ p : P, |v (y p)| := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Complex.norm_mul, Complex.norm_prod]
      simp only [Complex.norm_real, Real.norm_eq_abs]

section Bounds

variable {n : ℕ} {F P I : Type*}
variable [Fintype F] [DecidableEq F] [Fintype P] [DecidableEq P]
variable [Fintype I] [DecidableEq I]
variable (e : Fin n ≃ F ⊕ P) (T : (Fin n → I) → ℂ) (v : I → ℝ)

/-- A fixed free port retains the original marginal, paying one vector bound
for each physical slot. The original table need not be symmetric. -/
theorem fixed_free_marginal (A D : ℝ) (hD : 1 ≤ D)
    (hv : (∑ i, |v i|) ≤ D)
    (hT : ∀ k i, (∑ z : Fin n → I, if z k = i then ‖T z‖ else 0) ≤ A)
    (f : F) (i : I) :
    (∑ x : F → I, if x f = i then ‖contract e T v x‖ else 0) ≤
      A * D ^ Fintype.card P := by
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hp := vector_point_le v D hv
  have hn (x : F → I) :
      ‖contract e T v x‖ ≤ (∑ y : P → I, ‖T (assemble e x y)‖) *
        D ^ Fintype.card P := by
    calc
      ‖contract e T v x‖ ≤
          ∑ y : P → I, ‖T (assemble e x y)‖ * ∏ p : P, |v (y p)| :=
        norm_contract_le e T v x
      _ ≤ ∑ y : P → I, ‖T (assemble e x y)‖ * D ^ Fintype.card P := by
        apply Finset.sum_le_sum
        intro y _hy
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        simpa only [Finset.card_univ] using vector_product_le v D hp Finset.univ y
      _ = (∑ y : P → I, ‖T (assemble e x y)‖) * D ^ Fintype.card P := by
        rw [Finset.sum_mul]
  have hm :
      (∑ x : F → I, if x f = i then ∑ y : P → I, ‖T (assemble e x y)‖ else 0) ≤ A := by
    have hs :=
      sum_assemble e (fun z => if z (e.symm (Sum.inl f)) = i then ‖T z‖ else 0)
    simp only [assemble_free] at hs
    have heq :
        (∑ x : F → I, if x f = i then ∑ y : P → I, ‖T (assemble e x y)‖ else 0) =
          ∑ x : F → I, ∑ y : P → I, if x f = i then ‖T (assemble e x y)‖ else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx : x f = i
      · simp only [if_pos hx]
      · simp only [if_neg hx, Finset.sum_const_zero]
    rw [heq, hs]
    exact hT (e.symm (Sum.inl f)) i
  calc
    (∑ x : F → I, if x f = i then ‖contract e T v x‖ else 0) ≤
        ∑ x : F → I,
          (if x f = i then ∑ y : P → I, ‖T (assemble e x y)‖ else 0) *
            D ^ Fintype.card P := by
      apply Finset.sum_le_sum
      intro x _hx
      by_cases hx : x f = i
      · simpa only [if_pos hx] using hn x
      · simp only [if_neg hx, zero_mul, le_refl]
    _ = (∑ x : F → I,
        if x f = i then ∑ y : P → I, ‖T (assemble e x y)‖ else 0) *
          D ^ Fintype.card P := by rw [Finset.sum_mul]
    _ ≤ A * D ^ Fintype.card P :=
      mul_le_mul_of_nonneg_right hm (pow_nonneg hD0 _)

/-- A physical port supplies a genuine anchor for the whole free-coordinate
sum. The nonnegative budget also covers an empty alphabet without an inhabitant. -/
theorem whole_free_sum (A D : ℝ) (hA : 0 ≤ A) (hD : 1 ≤ D)
    (hv : (∑ i, |v i|) ≤ D)
    (hT : ∀ k i, (∑ z : Fin n → I, if z k = i then ‖T z‖ else 0) ≤ A)
    (p0 : P) :
    (∑ x : F → I, ‖contract e T v x‖) ≤ A * D ^ Fintype.card P := by
  classical
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hp := vector_point_le v D hv
  let rest : Finset P := Finset.univ.erase p0
  have hk : rest.card + 1 = Fintype.card P := by
    exact Finset.card_erase_add_one (Finset.mem_univ p0)
  have hprod (z : Fin n → I) :
      (∏ p : P, |v (z (e.symm (Sum.inr p)))|) ≤
        |v (z (e.symm (Sum.inr p0)))| * D ^ rest.card := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun p => |v (z (e.symm (Sum.inr p)))|) (Finset.mem_univ p0)]
    exact mul_le_mul_of_nonneg_left
      (vector_product_le v D hp rest (fun p => z (e.symm (Sum.inr p)))) (abs_nonneg _)
  have hweighted :
      (∑ z : Fin n → I, ‖T z‖ * |v (z (e.symm (Sum.inr p0)))|) ≤ A * D :=
    weighted_fiber_le T (fun z => z (e.symm (Sum.inr p0))) v A D hA
      (hT (e.symm (Sum.inr p0))) hv
  calc
    (∑ x : F → I, ‖contract e T v x‖) ≤
        ∑ x : F → I, ∑ y : P → I, ‖T (assemble e x y)‖ * ∏ p : P, |v (y p)| :=
      Finset.sum_le_sum (fun x _ => norm_contract_le e T v x)
    _ = ∑ z : Fin n → I, ‖T z‖ * ∏ p : P, |v (z (e.symm (Sum.inr p)))| := by
      simpa only [assemble_physical] using
        sum_assemble e (fun z => ‖T z‖ * ∏ p : P, |v (z (e.symm (Sum.inr p)))|)
    _ ≤ ∑ z : Fin n → I,
        (‖T z‖ * |v (z (e.symm (Sum.inr p0)))|) * D ^ rest.card := by
      apply Finset.sum_le_sum
      intro z _hz
      calc
        ‖T z‖ * (∏ p : P, |v (z (e.symm (Sum.inr p)))|) ≤
            ‖T z‖ * (|v (z (e.symm (Sum.inr p0)))| * D ^ rest.card) :=
          mul_le_mul_of_nonneg_left (hprod z) (norm_nonneg _)
        _ = (‖T z‖ * |v (z (e.symm (Sum.inr p0)))|) * D ^ rest.card :=
          (mul_assoc _ _ _).symm
    _ = (∑ z : Fin n → I, ‖T z‖ * |v (z (e.symm (Sum.inr p0)))|) *
        D ^ rest.card := by rw [Finset.sum_mul]
    _ ≤ (A * D) * D ^ rest.card :=
      mul_le_mul_of_nonneg_right hweighted (pow_nonneg hD0 _)
    _ = A * D ^ Fintype.card P := by
      rw [mul_assoc, ← pow_succ', hk]

end Bounds

end

end YM.Integration.OrderedPhysicalTensorContraction
