import YM.Integration.ActualRunQlocalNativeTuple
import YM.Comparison.Density.Payload.Testing

/-! The original finite-jet reader is attached to the original full stub.
The address relation records equality of this specific native reading; it
makes no identification of translated tests or omitted endpoints. Coefficient
linearity uses the proved signed complex-linear reader. Unit-test bounds
retain its full basis, affine and height costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunQlocalNativeTuple
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open RG05Readout RG05Readout.Native RG05Readout.Address
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {p L n : ℕ} {hn : n ≤ L}
  {V : Type} [DecidableEq V] (D : Datum R p L n hn V)

def readerRegion : Comparison.Density.Testing.Region
    (fun i => (orbit D i).Mood) (R.family.side L p) where
  knows i S f g := (positions D).stub i ⊆ S → reader D i f = reader D i g
  reflexive _ _ _ _ := rfl
  tighter _ _ _ h _ _ he hs := he (hs.trans h)

def labelCoefficient (i : V)
    (j : (R.family.labels.level (grade D i)).Index)
    (x : TestSpace (orbit D)) : ℂ := reader D i (x i) * label D i j

omit [DecidableEq V] in
/-- All allowed test dependence is at the original slot and full stub. -/
theorem coefficient_reads (i : V)
    (j : (R.family.labels.level (grade D i)).Index)
    (S : Support (R.family.side L p)) (hS : (positions D).stub i ⊆ S) :
    Comparison.Density.Testing.Reads (readerRegion D) S {i}
      (labelCoefficient D i j) := by
  intro x y h
  exact congrArg (fun z : ℂ => z * label D i j)
    (h i (Finset.mem_singleton_self i) hS)

/-- Signed native orientation has already been absorbed in this linear map. -/
theorem coefficient_letter (i : V)
    (j : (R.family.labels.level (grade D i)).Index) :
    RG3.Held.Letter ℂ (fun i => (orbit D i).Mood) {i}
      (labelCoefficient D i j) := by
  have h : RG3.Held.Letter ℂ (fun i => (orbit D i).Mood) {i}
      (fun x => reader D i (x i)) := by
    constructor
    · intro x y he
      exact congrArg (reader D i) (he i (Finset.mem_singleton_self i))
    · intro x k hk a b
      have he : k = i := Finset.mem_singleton.mp hk
      subst k
      simp
    · intro x k hk a b
      have he : k = i := Finset.mem_singleton.mp hk
      subst k
      simp
  have he : labelCoefficient D i j =
      (fun x : TestSpace (orbit D) => label D i j * reader D i (x i)) := by
    funext x
    exact mul_comm _ _
  rw [he]
  exact h.cmul (label D i j)

omit [DecidableEq V] in
/-- The literal coefficient bound is pointwise in the actual unit test. -/
theorem coefficient_bound (i : V)
    (j : (R.family.labels.level (grade D i)).Index)
    (x : IndependentTests (orbit D)) :
    ‖labelCoefficient D i j (testInclusion (orbit D) x)‖ ≤
      (‖constant D i‖ *
        ((((R.family.S.toDepth hn p).count.val : ℝ)⁻¹) ^ depth (D.choice i).2.1 *
          (NativeCalibrationMoodReadout.coordinateCost (depth (D.choice i).2.1) *
            (orbit D i).height (ActualRunCalibrationTests.coordinates.symm
              (RG05Readout.Flatten.placeR (R.family.S.toDepth hn p) (D.choice i).1))))) *
        ‖label D i j‖ := by
  unfold labelCoefficient
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [mul_one] using
    reader_bound D i (testInclusion (orbit D) x i) (x i).property

end YM.Integration.ActualRunQlocalNativeTuple
end
