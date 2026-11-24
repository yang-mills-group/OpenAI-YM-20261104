import YM.Integration.WilsonIndependentExactPlate

/-! The reported length is an actual ratio of lattice sizes on the matched
inversion board. Its clock charge is controlled by the one physical period. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentExactReportWidth
open RegulatorIR RegulatorIR.Geometry WilsonIndependentExactPlate

theorem original (V:XSpace.Run)(a j:ℕ)(ha:0<a)(hj:4 ≤ j)(w:Requests a):
    let C:=S V a ha j hj
    1 ≤ C.l (report V a w) ∧ C.l (report V a w) ≤ ((V.step w.val).p.side.val:ℝ) := by
  intro C
  have den:1 ≤ (↑(V.ratio^w.val):ℝ):=by exact_mod_cast V.den_pos w.val
  have units: (↑(V.ratio^w.val):ℝ)⁻¹*C.l (report V a w)=1:=(units V a ha j hj w).2
  have positive:0<(↑(V.ratio^w.val):ℝ):=lt_of_lt_of_le zero_lt_one den
  have eq:C.l (report V a w)=(↑(V.ratio^w.val):ℝ):=by
    calc
      _ = (↑(V.ratio^w.val):ℝ)*((↑(V.ratio^w.val):ℝ)⁻¹*C.l (report V a w)) := by
        rw [←mul_assoc,mul_inv_cancel₀ positive.ne',one_mul]
      _ = _ := by rw [units,mul_one]
  refine ⟨den.trans_eq eq.symm,?_⟩
  change ((V.step w.val).p.side.val:ℝ)/((n V a (report V a w)).val:ℝ) ≤ _
  have board:1 ≤ ((n V a (report V a w)).val:ℝ):=by exact_mod_cast (n V a (report V a w)).pos
  exact div_le_self (by positivity) board

theorem logarithm (V:XSpace.Run)(a j:ℕ)(ha:0<a)(hj:4 ≤ j)(w:Requests a):
    |Real.log ((S V a ha j hj).l (report V a w))| ≤ Real.log ((V.step w.val).p.side.val:ℝ) := by
  obtain ⟨lo,hi⟩:=original V a j ha hj w
  rw [abs_of_nonneg (Real.log_nonneg lo)]
  exact Real.log_le_log (zero_lt_one.trans_le lo) hi

end YM.Integration.WilsonIndependentExactReportWidth
