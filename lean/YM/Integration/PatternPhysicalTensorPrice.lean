import YM.Integration.PatternSlotCoordinates
import YM.Integration.FixedArgumentMultilinear
import YM.Integration.FixedCouplingPhysicalBound

/-! Price the literal fixed-pattern tensor after expanding only its physical
arguments. Coupling slots and the original normalized tensor remain fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PatternPhysicalTensorPrice
open Function PatternTensorRows PatternSlotCoordinates
open scoped BigOperators Classical

variable {I J E : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complete ordered coupling/field table of the original tensor. -/
def table {n : ℕ} (c : E) (φ : (I → ℝ) →L[ℝ] E)
    (T : Tensor.T E ℂ n) (z : Fin n → Option I) : ℂ :=
  T (fun k => (z k).elim c (fun i => φ (Pi.single i 1)))

private theorem basis_sum (v : I → ℝ) :
    (∑ i, v i • Pi.single i 1) = v := by
  ext i
  rw [Finset.sum_apply]
  simp [Pi.single_apply]

private theorem image_sum (φ : (I → ℝ) →L[ℝ] E) (v : I → ℝ) :
    φ v = ∑ i, v i • φ (Pi.single i 1) := by
  calc
    _ = φ (∑ i, v i • Pi.single i 1) := congrArg φ (basis_sum v).symm
    _ = _ := by rw [map_sum]; simp only [map_smul]

omit [Fintype J] in
/-- Exact physical expansion; Gaussian and coupling slots keep their inputs. -/
theorem value_eq {n : ℕ} (p : Fin n → Kind) (c : E)
    (φ : (I → ℝ) →L[ℝ] E) (ι : J ↪ I)
    (L : (J → ℝ) →ₗ[ℝ] E) (M : (Unit → ℝ) →ₗ[ℝ] E)
    (v : I → ℝ) (T : Tensor.T E ℂ n)
    (hL : ∀ j, L (Pi.single j 1) = φ (Pi.single (ι j) 1))
    (hM : M (Pi.single () 1) = φ v) (x : Internal p → J) :
    PatternTensorRows.tensorValue c L M T ⟨p, (x, fun _ => ())⟩ =
      FixedCouplingPhysicalBound.value (couplingSplit p) (fieldEquiv p)
        (table c φ T) v (ι ∘ x) := by
  rw [tensorValue_physical]
  simp_rw [hM, image_sum φ v]
  simp only [Function.comp_def]
  rw [FixedArgumentMultilinear.expand_physical_slots (physicalSplit p) T
    (Sum.elim (fun _ : Coupling p => c) (fun g => L (Pi.single (x g) 1)))
    (fun i => φ (Pi.single i 1)) v]
  unfold FixedCouplingPhysicalBound.value OrderedPhysicalTensorContraction.contract
  apply Finset.sum_congr rfl
  intro y _hy
  rw [Complex.real_smul, Complex.ofReal_prod, mul_comm]
  congr 1
  unfold FixedCouplingPhysicalBound.fieldTable table
  apply congrArg (fun z : Fin n → E => T z)
  funext k
  cases hk : kindSplit p k with
  | inl u =>
    simp [physicalSplit, couplingSplit, Equiv.sumCongr, hk,
      FixedNoneCoordinateRestriction.fill, OrderedPhysicalTensorContraction.assemble]
  | inr u =>
    cases u <;> simp [physicalSplit, couplingSplit, Equiv.sumCongr, hk,
      FixedNoneCoordinateRestriction.fill, OrderedPhysicalTensorContraction.assemble, hL]

/-- Full state sum when an original physical position supplies the anchor. -/
theorem physical_sum {n : ℕ} (p : Fin n → Kind) (c : E)
    (φ : (I → ℝ) →L[ℝ] E) (ι : J ↪ I)
    (L : (J → ℝ) →ₗ[ℝ] E) (M : (Unit → ℝ) →ₗ[ℝ] E)
    (v : I → ℝ) (T : Tensor.T E ℂ n)
    (hL : ∀ j, L (Pi.single j 1) = φ (Pi.single (ι j) 1))
    (hM : M (Pi.single () 1) = φ v)
    (A D : ℝ) (hA : 0 ≤ A) (hD : 1 ≤ D) (hv : (∑ i, |v i|) ≤ D)
    (hT : ∀ k i, (∑ z : Fin n → Option I,
      if z k = some i then ‖table c φ T z‖ else 0) ≤ A)
    (p0 : External p) :
    (∑ x : Internal p → J,
      ‖PatternTensorRows.tensorValue c L M T ⟨p, (x, fun _ => ())⟩‖) ≤
      A * D ^ Fintype.card (External p) := by
  simp_rw [value_eq p c φ ι L M v T hL hM]
  exact FixedCouplingPhysicalBound.physical_sum (couplingSplit p) (fieldEquiv p)
    (table c φ T) v ι A D hD hv hT hA p0

/-- A fixed original Gaussian position keeps its full fiber marginal. -/
theorem gaussian_marginal {n : ℕ} (p : Fin n → Kind) (c : E)
    (φ : (I → ℝ) →L[ℝ] E) (ι : J ↪ I)
    (L : (J → ℝ) →ₗ[ℝ] E) (M : (Unit → ℝ) →ₗ[ℝ] E)
    (v : I → ℝ) (T : Tensor.T E ℂ n)
    (hL : ∀ j, L (Pi.single j 1) = φ (Pi.single (ι j) 1))
    (hM : M (Pi.single () 1) = φ v)
    (A D : ℝ) (hD : 1 ≤ D) (hv : (∑ i, |v i|) ≤ D)
    (hT : ∀ k i, (∑ z : Fin n → Option I,
      if z k = some i then ‖table c φ T z‖ else 0) ≤ A)
    (k : Internal p) (i : J) :
    (∑ x : Internal p → J, if x k = i then
      ‖PatternTensorRows.tensorValue c L M T ⟨p, (x, fun _ => ())⟩‖ else 0) ≤
      A * D ^ Fintype.card (External p) := by
  simp_rw [value_eq p c φ ι L M v T hL hM]
  convert FixedCouplingPhysicalBound.gaussian_marginal (couplingSplit p) (fieldEquiv p)
    (table c φ T) v ι A D hD hv hT k i using 1
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> rfl

end YM.Integration.PatternPhysicalTensorPrice
end
