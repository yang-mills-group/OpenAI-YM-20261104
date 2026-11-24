import YM.Integration.ActualInputVertexTable
import YM.Integration.NativePaidStationaryArray
import YM.Integration.FiniteVacuumProgramBound

/-! Exact pattern prices for the original input and its actual one-bond ray.
The Gaussian alphabet stays in the free-fine summand. The full stationary
ray retains the coarse identity and the copied-coarse subtraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualInputPatternPrice
open Function Filter Lattice Wilson RG Precision Tree Exterior Marker
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Push.Uniform Stationary RG08.Line Comparison.RG02 PhysicalNext.Repeat.Legato
open PatternTensorRows ActualInputVertexTable
open scoped Topology BigOperators Classical ContDiff

/-- A harmless unit enlargement of the actual paid ray bill. -/
def rayCost {G : Gauge} (T : Run G) (i : ℕ) : ℝ :=
  1 + (2 + (Fintype.card (Loc G 1) : ℝ) * Real.exp 4) *
    (Real.log (T.family.path.levels.clock.hatBeta i)) ^ 6

private theorem rayCost_ge_one {G : Gauge} (T : Run G) (i : ℕ) :
    1 ≤ rayCost T i := by
  unfold rayCost
  have h : 0 ≤ (2 + (Fintype.card (Loc G 1) : ℝ) * Real.exp 4) *
      (Real.log (T.family.path.levels.clock.hatBeta i)) ^ 6 := by positivity
  linarith

private theorem gaussian_basis {G : Gauge} {c f : Side} {S : StepData c f}
    (F : Forest S.ratio) (i : Precision.Key F G) :
    Bulk.hinge F (Pi.single i 1) = fieldFrame F (Pi.single (Sum.inr i) 1) := by
  have h := ActualJointCoordinateMap.gaussian_value F (Pi.single i 1)
  rw [ActualJointCoordinateMap.field_vector_value] at h
  rw [← h]
  change (0, paint F G (Sum.elim (fun _ => 0) (Pi.single i 1))) =
    (0, paint F G (Pi.single (Sum.inr i) 1))
  apply congrArg (fun z : Positions (Push.Uniform.Joint F G) => (0, paint F G z))
  funext z
  cases z <;> simp [Pi.single_apply]

private theorem ray_basis {G : Gauge} {c f : Side} {S : StepData c f}
    {p : Clip} {P : PathData G} {O : ChartRatio G}
    (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (B : fieldDir G c 1) :
    ActualGroundContraction.rayMap K F B (Pi.single () 1) =
      fieldFrame F ((paint F G).symm (Bulk.classical S F (K.b F) B)) := by
  simp [ActualGroundContraction.rayMap, fieldFrame]

/-- One event precedes every original datum, input, test and slot pattern. -/
theorem patterns {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (A : NumericSchedule T.family J) :
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℕ, ∀ᶠ i : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = i →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (x : TestSpace J.tests)
        (t : (T.family.path.levels.clock.op datum.level datum.period).Choices),
      let F := green (T.family.path.levels.clock.op datum.level datum.period)
      let B := NativeNormalizedBondTest.actualField T hG datum.level datum.period
      FiniteVacuumProgramBound.PatternPrice (ActualGroundProgram.coupling F)
        (Bulk.hinge F) (ActualGroundContraction.rayMap (datum.kernel Y) F B)
        (Bulk.geometric (datum.kernel Y) F t (I.colors x)) J.order
        (1 + C * (A.admittedCost i) ^ e) (rayCost T i) := by
  obtain ⟨C, hC, e, h⟩ := ActualInputVertexTable.vertices T hG hT (R := R) A
  refine ⟨C, hC, e, ?_⟩
  filter_upwards [h] with i hi
  intro datum hlevel Y I x t
  subst i
  dsimp only
  let F := green (T.family.path.levels.clock.op datum.level datum.period)
  let B := NativeNormalizedBondTest.actualField T hG datum.level datum.period
  let K := datum.kernel Y
  let v := (paint F G).symm (Bulk.classical _ F (K.b F) B)
  let ι : Precision.Key F G ↪ Push.Uniform.Joint F G :=
    ⟨Sum.inr, by intro a b h; exact Sum.inr.inj h⟩
  let price := 1 + C * (A.admittedCost datum.level) ^ e
  let D := rayCost T datum.level
  have hA : 0 ≤ price := by
    have hW := A.admitted_cost_ge_one datum.level
    dsimp only [price]
    positivity
  have hD : 1 ≤ D := rayCost_ge_one T datum.level
  have hv : (∑ q, |v q|) ≤ D := by
    have hr := NativePaidStationaryArray.actualRay_paid T Y datum.cutoff
      datum.period datum.level datum.below hG hT t
    have he : (∑ q, |v q|) ≤
        (2 + (Fintype.card (Loc G 1) : ℝ) * Real.exp 4) *
          (Real.log (T.family.path.levels.clock.hatBeta datum.level)) ^ 6 := by
      exact hr
    exact he.trans (le_add_of_nonneg_left zero_le_one)
  have hL : ∀ j, Bulk.hinge F (Pi.single j 1) =
      fieldFrame F (Pi.single (ι j) 1) := fun j => gaussian_basis F j
  have hM : ActualGroundContraction.rayMap K F B (Pi.single () 1) =
      fieldFrame F v := ray_basis K F B
  have htable (j : ℕ) (hj : j ≤ J.order) :
      ∀ k a, (∑ z : Fin (j + 2) → Option (Push.Uniform.Joint F G),
        if z k = some a then
          ‖PatternPhysicalTensorPrice.table (1, 0) (fieldFrame F)
            (complexCoeff (Bulk.geometric K F t (I.colors x)) (j + 2)) z‖
        else 0) ≤ price := by
    intro k a
    have ht := hi datum rfl Y I x F t (j + 1) (by omega) k a
    exact ht.trans (le_add_of_nonneg_left zero_le_one)
  change FiniteVacuumProgramBound.PatternPrice (ActualGroundProgram.coupling F)
    (Bulk.hinge F) (ActualGroundContraction.rayMap K F B)
    (Bulk.geometric K F t (I.colors x)) J.order price D
  constructor
  · intro j _hj hj p p0
    have hu : (default : External p → Unit) = (fun _ => ()) := Subsingleton.elim _ _
    have hp := PatternPhysicalTensorPrice.physical_sum p (1, 0) (fieldFrame F) ι
      (Bulk.hinge F) (ActualGroundContraction.rayMap K F B) v
      (complexCoeff (Bulk.geometric K F t (I.colors x)) (j + 2))
      hL hM price D hA hD hv (htable j hj) p0
    simpa only [FiniteVacuumProgramBound.normalizedValue, complexCoeff, State,
      Fintype.sum_prod_type, Fintype.sum_unique, hu, ActualGroundProgram.coupling] using hp
  · intro j _hj hj p k a
    have hu : (default : External p → Unit) = (fun _ => ()) := Subsingleton.elim _ _
    have hp := PatternPhysicalTensorPrice.gaussian_marginal p (1, 0) (fieldFrame F) ι
      (Bulk.hinge F) (ActualGroundContraction.rayMap K F B) v
      (complexCoeff (Bulk.geometric K F t (I.colors x)) (j + 2))
      hL hM price D hD hv (htable j hj) k a
    simpa only [FiniteVacuumProgramBound.normalizedValue, complexCoeff, State,
      Fintype.sum_prod_type, Fintype.sum_unique, hu, ActualGroundProgram.coupling] using hp

end YM.Integration.ActualInputPatternPrice
end
