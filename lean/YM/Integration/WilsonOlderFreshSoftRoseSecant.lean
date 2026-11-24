import YM.Integration.WilsonOriginalTwoFlatRoseNominated

/-! The independently stopped scalar and the remaining measured incidence use one physical secant. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftRoseSecant
open Function Finset MeasureTheory Lattice RG Wilson Source Labels
open PhysicalNext.Repeat.Legato Planned.GuardedAtom Trace.Physical.GermGraph
open WilsonOriginalTwoFlatRoseNominated (face)
open WilsonMaxwellThermometerNominatedCofactor (native)
open WilsonMaxwellThermometerNominatedSecant (bill)
open OPE OPE.Orbits Extraction Spec Table XSpace XSpace.Rose
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(A:WilsonPositionThermometerCapStation.Group R.family 6){N per:ℕ}
local notation "Sites" => Site (R.family.side N per)
local notation "Faces" => Finset (Fin 3)

def actual (y:Sites×Sites)(s:Faces):ℂ:=R.family.omega N per (face R A y s)

def deficit (φ:Test 3)(r:ℝ)(F Q:Sites×Sites → Faces → ℂ):ℂ:=
  ∑y:Sites×Sites,WilsonThermometerAlignedCells.mass (R:=R) r (N,per) φ y*
    ((WilsonMaxwellThermometerNominatedCofactor.reading R A N per y (native R A N per y 0)-
      WilsonPositionThermometerConnected.value (Q y))-
       ∑s:Faces,bill (actual R A y) (Q y) s*(actual R A y s-F y s))

theorem balance (φ:Test 3)(r:ℝ)(F Q:Sites×Sites → Faces → ℂ):
    deficit R A φ r F Q=∑y:Sites×Sites,WilsonThermometerAlignedCells.mass (R:=R) r (N,per) φ y*
      ∑s:Faces,bill (actual R A y) (Q y) s*(F y s-Q y s):=by
  unfold deficit
  apply sum_congr rfl
  intro y _
  apply congrArg (_*·)
  rw [WilsonMaxwellThermometerNominatedCofactor.original,WilsonMaxwellThermometerNominatedSecant.signed]
  change (∑s:Faces,bill (actual R A y) (Q y) s*(actual R A y s-Q y s))-_ = _
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro s _
  ring

theorem priced (φ:Test 3)(r:ℝ)(F Q:Sites×Sites → Faces → ℂ)(fare:Faces→ℝ)
    (small:∀y s,‖F y s-Q y s‖≤fare s):
    ‖deficit R A φ r F Q‖≤∑y:Sites×Sites,‖WilsonThermometerAlignedCells.mass (R:=R) r (N,per) φ y‖*
      ∑s:Faces,‖bill (actual R A y) (Q y) s‖*fare s:=by
  rw [balance]
  refine (norm_sum_le ..).trans (sum_le_sum fun y _=>?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum fun s _=>by
    rw [norm_mul];exact mul_le_mul_of_nonneg_left (small y s) (norm_nonneg _))) (norm_nonneg _)

theorem tested (φ:Test 3)(r:ℝ)(F Q:Sites×Sites → Faces → ℂ)(fare:Faces→ℝ)(limit:ℝ)(pos:0≤limit)
    (small:∀y s,‖F y s-Q y s‖≤fare s)
    (inverse:∀y,∑s:Faces,‖bill (actual R A y) (Q y) s‖*fare s≤limit):
    ‖deficit R A φ r F Q‖≤(∫x:Points 3,‖φ x‖)*limit:=by
  refine (priced R A φ r F Q fare small).trans ?_
  calc
    _ ≤ ∑y:Sites×Sites,‖WilsonThermometerAlignedCells.mass (R:=R) r (N,per) φ y‖*limit:=
      sum_le_sum fun y _=>mul_le_mul_of_nonneg_left (inverse y) (norm_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm
    _ ≤ _ :=mul_le_mul_of_nonneg_right (WilsonThermometerAlignedCells.variation (R:=R) r (N,per) φ) pos

end YM.Integration.WilsonOlderFreshSoftRoseSecant
end
