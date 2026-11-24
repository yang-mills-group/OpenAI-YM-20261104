import YM.Integration.WilsonOriginalTwoFlatRoseNominated

/-! On the original finite relative mesh, the price of a uniformly restored
ordinary error involves two proper factors and the variation of the filed test. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseVariation
open Function Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories RG16.Literal
open PhysicalNext.Repeat.Legato Planned.GuardedAtom Trace.Physical.GermGraph
open OPE OPE.Orbits Extraction Spec Table XSpace XSpace.Rose
open WilsonOriginalTwoFlatRoseNominated WilsonMaxwellThermometerNominatedSecant
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(A:WilsonPositionThermometerCapStation.Group R.family 6){N per:ℕ}
local notation "S" => Site (R.family.side N per)
local notation "E" => Finset (Fin 3)

theorem original (φ:Test 3)(r:ℝ)(Q:S×S → E → ℂ)(a b ε:ℝ)(ep:0≤ε):
    let μ:=WilsonThermometerAlignedCells.mass (R:=R) r (N,per) φ
    let Y(y:S×S)(s:E):=R.family.omega N per (face R A y s)
    let T:=max 1 (max a b)
    (∀y,μ y≠0 → ∀s:E,s.Nonempty → s≠univ → ‖Y y s‖≤a) →
    (∀y,μ y≠0 → ∀i:Fin 3,‖Q y {i}‖≤b) →
    (∀y,μ y≠0 → ∀s:E,s.Nonempty → ‖Y y s-Q y s‖≤ε) →
    ‖∑y:S×S,μ y*(WilsonMaxwellThermometerNominatedCofactor.reading R A N per y
        (WilsonMaxwellThermometerNominatedCofactor.native R A N per y 0)-
      WilsonPositionThermometerConnected.value (Q y))‖≤(∫x:Points 3,‖φ x‖)*(7*(T+2*T^2)*ε):=by
  classical
  intro μ Y T proper seed earned
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑y:S×S,‖μ y‖*(7*(T+2*T^2)*ε):=by
      apply sum_le_sum
      intro y _
      rw [norm_mul]
      by_cases nz:μ y=0
      · simp [nz]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [WilsonMaxwellThermometerNominatedCofactor.original,WilsonMaxwellThermometerNominatedSecant.signed]
      apply (norm_sum_le ..).trans
      calc
        _ ≤ ∑s:E,‖bill (Y y) (Q y) s‖*ε:=by
          apply sum_le_sum
          intro s _
          rw [norm_mul]
          by_cases ne:s.Nonempty
          · exact mul_le_mul_of_nonneg_left (earned y nz s ne) (norm_nonneg _)
          · have none (t:Fin 7): (∅:E)≠faceKey t:=by fin_cases t <;> decide
            rw [not_nonempty_iff_eq_empty.mp ne]
            simp [bill,none]
        _ = (∑s:E,‖bill (Y y) (Q y) s‖)*ε:=(sum_mul ..).symm
        _ ≤ 7*(T+2*T^2)*ε:=mul_le_mul_of_nonneg_right (budget (Y y) (Q y) a b (proper y nz) (seed y nz)) ep
    _ = (∑y:S×S,‖μ y‖)*(7*(T+2*T^2)*ε):=(sum_mul ..).symm
    _ ≤ _:=by
      have pos:0≤T:=zero_le_one.trans (le_max_left _ _)
      exact mul_le_mul_of_nonneg_right (WilsonThermometerAlignedCells.variation (R:=R) r (N,per) φ) (by positivity)

end YM.Integration.WilsonOriginalTwoFlatRoseVariation
end
