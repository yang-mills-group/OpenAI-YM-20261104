import YM.Integration.WilsonPositionThermometerGradedReading

/-! Translate the three fitted cutoff fields together on their original
finite Wilson law. The signed field of grade six sits at the origin and the
two fields of grade four retain their independent fine-lattice displacements. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerAlignedCells
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb Trace.Pilot RG12 RG17 PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose Cells Push.GridApprox
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading
open scoped Topology Classical BigOperators

section Triples
variable {T : Type} [AddCommGroup T]

def offsets (x : Fin 3 → T) : T × T := (x 1 - x 0, x 2 - x 0)

def atOrigin (y : T × T) : Fin 3 → T := ![0,y.1,y.2]

def placedAt (y : T × T) (c : T) : Fin 3 → T := fun i => atOrigin y i + c

private def triples : (Fin 3 → T) ≃ (T × T) × T where
  toFun x := (offsets x,x 0)
  invFun yc := placedAt yc.1 yc.2
  left_inv x := by
    funext j
    fin_cases j <;> simp [placedAt,atOrigin,offsets]
  right_inv := by
    rintro ⟨⟨y,z⟩,c⟩
    simp [placedAt,atOrigin,offsets]

variable [Fintype T]

private theorem sum_triples {M : Type} [AddCommMonoid M] (f : (Fin 3 → T) → M) :
    ∑ x, f x = ∑ y, ∑ c, f (placedAt y c) := by
  calc
    _ = ∑ q : (T × T) × T, f (placedAt q.1 q.2) :=
      Fintype.sum_equiv triples _ _ (fun x => congrArg f (triples.left_inv x).symm)
    _ = _ := Fintype.sum_prod_type _

end Triples

variable {G : Gauge} {R : Run G} (A : Group R.family 6) (r : ℝ) (z : UVIndex)
local notation "T" => Site (R.family.side z.1 z.2)
local notation "χ" => WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z

def mass (φ : Test 3) (y : T × T) : ℂ :=
  ∑ c, WilsonSeparatedOriginalThermometerCells.weight φ χ (placedAt y c)

theorem variation (φ : Test 3) :
    ∑ y, ‖mass (R:=R) r z φ y‖ ≤ ∫ x : Points 3, ‖φ x‖ := by
  calc
    _ ≤ ∑ y, ∑ c, ‖WilsonSeparatedOriginalThermometerCells.weight φ χ (placedAt y c)‖ :=
      sum_le_sum fun _ _ => norm_sum_le ..
    _ = _ := (sum_triples (fun x => ‖WilsonSeparatedOriginalThermometerCells.weight φ χ x‖)).symm
    _ ≤ _ := WilsonSeparatedOriginalThermometerCells.variation φ χ
      (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)

/-- A nonzero relative cell has a genuine lift with a nonzero value of the
original test. This retains the test's separation at the three occupied sites. -/
theorem supported (φ : Test 3) {y : T × T} (hm : mass (R:=R) r z φ y ≠ 0) :
    ∃ c : T, ∃ x : Points 3, φ x ≠ 0 ∧ χ x = placedAt y c := by
  by_contra! none
  apply hm
  apply sum_eq_zero
  intro c _
  unfold WilsonSeparatedOriginalThermometerCells.weight
  have vanishes : ∀ x : Points 3,
      (χ ⁻¹' {placedAt y c}).indicator (fun v => φ v) x = 0 := by
    intro x
    by_cases hit : χ x = placedAt y c
    · rw [Set.indicator_of_mem (show x ∈ χ ⁻¹' {placedAt y c} from hit)]
      by_contra nonzero
      exact none c x nonzero hit
    · exact Set.indicator_of_notMem (show x ∉ χ ⁻¹' {placedAt y c} from hit) _
  simp_rw [vanishes]
  simp

theorem translated (ready : ∀ i, R.family.ref (grade i).val ≤ z.1) (y : T × T) (c : T) :
    row A z (placedAt y c) = row A z (atOrigin y) := by
  funext s
  let tokens (i : Fin 3) : R.family.book.Token :=
    ⟨(grade i).val,A.station.wheel.atCut z (index A (grade i)) (vector A s i)⟩
  exact R.family.anchored (p:=z.2) R.makes tokens ready c (atOrigin y)

/-- Any signed function of the complete table and both relative offsets
uses the same finite masses. In particular, products of proper moments are
formed at the same placement before the finite sum. -/
theorem tested (ready : ∀ i, R.family.ref (grade i).val ≤ z.1) (φ : Test 3)
    (read : T × T → (Badge → ℂ) → ℂ) :
    φ.applyTo (fun x => read (offsets (χ x)) (row A z (χ x))) =
      ∑ y, mass (R:=R) r z φ y * read y (row A z (atOrigin y)) := by
  rw [WilsonSeparatedOriginalThermometerCells.tested φ χ
    (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)
    (fun x => read (offsets x) (row A z x)), sum_triples]
  apply sum_congr rfl
  intro y _
  rw [mass,sum_mul]
  apply sum_congr rfl
  intro c _
  rw [translated A z ready y c]
  have same : offsets (placedAt y c) = y := congrArg Prod.fst (triples.right_inv (y,c))
  rw [same]

theorem original {V : Normalize.Store G} (K : Pick V)
    (ready : ∀ i, R.family.ref (grade i).val ≤ z.1) :
    (Rose.test K).applyTo (full r A z) =
      ∑ y, mass (R:=R) r z (Rose.test K) y *
        WilsonPositionThermometerConnected.value (row A z (atOrigin y)) :=
  tested A r z ready (Rose.test K) (fun _ => WilsonPositionThermometerConnected.value)

/-- A scalar coefficient filed at each individual placement can be carried
inside the test mass even when it changes under a common translation. -/
def weighted (φ : Test 3) (coef : (Fin 3 → T) → ℂ) (y : T × T) : ℂ :=
  ∑ c, WilsonSeparatedOriginalThermometerCells.weight φ χ (placedAt y c) * coef (placedAt y c)

theorem weighted_variation (φ : Test 3) (coef : (Fin 3 → T) → ℂ) {B : ℝ} (pos : 0 ≤ B)
    (priced : ∀ o, WilsonSeparatedOriginalThermometerCells.weight φ χ o ≠ 0 → ‖coef o‖ ≤ B) :
    ∑ y, ‖weighted (R:=R) r z φ coef y‖ ≤ (∫ x : Points 3, ‖φ x‖) * B := by
  have term (o : Fin 3 → T) :
      ‖WilsonSeparatedOriginalThermometerCells.weight φ χ o * coef o‖ ≤
      ‖WilsonSeparatedOriginalThermometerCells.weight φ χ o‖ * B := by
    by_cases zero : WilsonSeparatedOriginalThermometerCells.weight φ χ o = 0
    · simp [zero]
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (priced o zero) (norm_nonneg _)
  calc
    _ ≤ ∑ y, ∑ c, ‖WilsonSeparatedOriginalThermometerCells.weight φ χ (placedAt y c) *
        coef (placedAt y c)‖ := sum_le_sum fun _ _ => norm_sum_le ..
    _ = _ := (sum_triples (fun o => ‖WilsonSeparatedOriginalThermometerCells.weight φ χ o * coef o‖)).symm
    _ ≤ ∑ o, ‖WilsonSeparatedOriginalThermometerCells.weight φ χ o‖ * B := sum_le_sum fun o _ => term o
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (WilsonSeparatedOriginalThermometerCells.variation φ χ
        (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)) pos

theorem weighted_read {I : Type} [Fintype I] (ready : ∀ i, R.family.ref (grade i).val ≤ z.1)
    (φ : Test 3) (coef : I → (Fin 3 → T) → ℂ) (read : I → (Badge → ℂ) → ℂ) :
    φ.applyTo (fun x => ∑ i, coef i (χ x) * read i (row A z (χ x))) =
      ∑ i, ∑ y, weighted (R:=R) r z φ (coef i) y * read i (row A z (atOrigin y)) := by
  rw [WilsonSeparatedOriginalThermometerCells.tested φ χ
    (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)
    (fun o => ∑ i, coef i o * read i (row A z o))]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_triples]
  apply sum_congr rfl
  intro y _
  rw [weighted,sum_mul]
  apply sum_congr rfl
  intro c _
  rw [translated A z ready y c,mul_assoc]

end YM.Integration.WilsonThermometerAlignedCells
end
