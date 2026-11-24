import YM.Integration.WilsonOriginalTwoFlatIRSocketBoundary
import YM.Integration.WilsonMaxwellThermometerNominatedSecant

/-! The measured fixed-ear entrance, captured two-ear difference and terminal Figure
share two signed boundary values. Restore their charges before the connected reading. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRSocketSale
open Finset WilsonMaxwellThermometerNominatedSecant WilsonPositionThermometerConnected
open scoped Classical BigOperators

structure Node (fixed figure basal last:ℂ)(upper month crossing terminal:ℝ):Prop where
  earned : ‖fixed-figure‖ ≤ (upper+month+crossing+‖basal‖+‖last‖)+terminal

theorem Node.on_fees {fixed figure basal last:ℂ}{upper month crossing terminal:ℝ}
    (L:Node fixed figure basal last upper month crossing terminal){low high:ℝ}
    (current:‖basal‖≤low)(birth:‖last‖≤high):
    ‖fixed-figure‖≤(upper+month+crossing+low+high)+terminal:=by
  linarith only [L.earned,current,birth]

theorem Node.at_phase {observed fixed figure basal last:ℂ}{upper month crossing terminal:ℝ}
    (L:Node fixed figure basal last upper month crossing terminal){phase low high:ℝ}
    (chamber:‖observed-fixed‖≤phase)(current:‖basal‖≤low)(birth:‖last‖≤high):
    ‖observed-figure‖≤phase+((upper+month+crossing+low+high)+terminal):=
  (norm_sub_le_norm_sub_add_norm_sub _ fixed _).trans (add_le_add chamber (L.on_fees current birth))

/-- At every occupied face apply its own earlier and later readings before restoring
    the exact signed connected secant on the original three-field row. -/
theorem connected (observed fixed figure basal last:Finset (Fin 3) → ℂ)
    (upper month crossing terminal phase low high:Finset (Fin 3) → ℝ)
    (nodes:∀s:Finset (Fin 3),s.Nonempty → Node (fixed s) (figure s) (basal s) (last s)
      (upper s) (month s) (crossing s) (terminal s))
    (chamber:∀s:Finset (Fin 3),s.Nonempty → ‖observed s-fixed s‖≤phase s)
    (current:∀s:Finset (Fin 3),s.Nonempty → ‖basal s‖≤low s)
    (birth:∀s:Finset (Fin 3),s.Nonempty → ‖last s‖≤high s):
    ‖value observed-value figure‖≤∑s:Finset (Fin 3),‖bill observed figure s‖*
      (phase s+((upper s+month s+crossing s+low s+high s)+terminal s)):=by
  rw [signed]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro s _
  rw [norm_mul]
  by_cases used:s.Nonempty
  · exact mul_le_mul_of_nonneg_left ((nodes s used).at_phase (chamber s used) (current s used) (birth s used)) (norm_nonneg _)
  · have clear:s=∅:=not_nonempty_iff_eq_empty.mp used
    rw [clear]
    have blank:bill observed figure ∅=0:=by
      have none (i:Fin 7):(∅:Finset (Fin 3))≠faceKey i:=by fin_cases i <;> decide
      simp [bill,none]
    simp [blank]

end YM.Integration.WilsonOriginalTwoFlatIRSocketSale
end
