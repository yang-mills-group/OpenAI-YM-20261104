import YM.Integration.FixedNoneCoordinateRestriction
import YM.Integration.FiniteCoordinateRestriction
import YM.Integration.OrderedPhysicalTensorContraction

/-! Fix all original coupling slots, contract only the physical slots, and
restrict the remaining field labels to the actual Gaussian alphabet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FixedCouplingPhysicalBound
open scoped BigOperators Classical

universe u v w x y
variable {n m : ℕ} {C : Type u} {F : Type v} {P : Type w}
    {I : Type x} {J : Type y}

/-- The original table with every coupling coordinate fixed at None. -/
def fieldTable (e : Fin n ≃ C ⊕ Fin m)
    (T : (Fin n → Option I) → ℂ) (z : Fin m → I) : ℂ :=
  T (FixedNoneCoordinateRestriction.fill e z)

/-- Only physical positions are contracted against the given field vector. -/
def value [Fintype P] [DecidableEq P] [Fintype I]
    (e : Fin n ≃ C ⊕ Fin m) (f : Fin m ≃ F ⊕ P)
    (T : (Fin n → Option I) → ℂ) (v : I → ℝ) (z : F → I) : ℂ :=
  OrderedPhysicalTensorContraction.contract f (fieldTable e T) v z

section Bounds
variable [Fintype F] [DecidableEq F] [Fintype P] [DecidableEq P]
    [Fintype I] [DecidableEq I] [Fintype J]
variable (e : Fin n ≃ C ⊕ Fin m) (f : Fin m ≃ F ⊕ P)
    (T : (Fin n → Option I) → ℂ) (v : I → ℝ) (ι : J ↪ I)
    (A D : ℝ) (hD : 1 ≤ D) (hv : (∑ i, |v i|) ≤ D)
    (hT : ∀ k i, (∑ z : Fin n → Option I,
      if z k = some i then ‖T z‖ else 0) ≤ A)

include hT in
private theorem field_marginal (k : Fin m) (i : I) :
    (∑ z : Fin m → I, if z k = i then ‖fieldTable e T z‖ else 0) ≤ A := by
  convert FixedNoneCoordinateRestriction.fixed_field_marginal e T k i
    (by
      convert hT (e.symm (Sum.inr k)) i using 1
      apply Finset.sum_congr rfl
      intro z _
      split_ifs <;> rfl) using 1
  apply Finset.sum_congr
  · ext z; simp
  · intro z _
    split_ifs <;> rfl

include hD hv hT in
/-- A genuine Gaussian port keeps its original anchored bound. -/
theorem gaussian_marginal (k : F) (i : J) :
    (∑ z : F → J, if z k = i then ‖value e f T v (ι ∘ z)‖ else 0) ≤
      A * D ^ Fintype.card P := by
  have hr := FiniteCoordinateRestriction.fixed_port_sum_le ι
    (fun z : F → I => ‖value e f T v z‖) (fun _ => norm_nonneg _) k i
  have hr' : (∑ z : F → J, if z k = i then ‖value e f T v (ι ∘ z)‖ else 0) ≤
      ∑ z : F → I, if z k = ι i then ‖value e f T v z‖ else 0 := by
    convert hr using 1
    all_goals
      apply Finset.sum_congr
      · ext z; simp
      · intro z _
        first | rfl | split_ifs <;> rfl
  exact hr'.trans (OrderedPhysicalTensorContraction.fixed_free_marginal
    f (fieldTable e T) v A D hD hv (field_marginal e T A hT) k (ι i))

include hD hv hT in
/-- An actual physical port supplies the anchor for the entire Gaussian sum. -/
theorem physical_sum (hA : 0 ≤ A) (p0 : P) :
    (∑ z : F → J, ‖value e f T v (ι ∘ z)‖) ≤
      A * D ^ Fintype.card P := by
  have hr := FiniteCoordinateRestriction.whole_sum_le ι
    (fun z : F → I => ‖value e f T v z‖) (fun _ => norm_nonneg _)
  have hr' : (∑ z : F → J, ‖value e f T v (ι ∘ z)‖) ≤
      ∑ z : F → I, ‖value e f T v z‖ := by
    convert hr using 1
    all_goals
      apply Finset.sum_congr
      · ext z; simp
      · intro z _
        rfl
  exact hr'.trans (OrderedPhysicalTensorContraction.whole_free_sum
    f (fieldTable e T) v A D hA hD hv (field_marginal e T A hT) p0)

end Bounds
end YM.Integration.FixedCouplingPhysicalBound
end
