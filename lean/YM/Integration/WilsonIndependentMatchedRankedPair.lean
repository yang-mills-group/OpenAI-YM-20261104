import YM.Integration.WilsonIndependentMatchedOrbitReading
import YM.Integration.WilsonOriginalPivotWardProduct

/-! A joint, grade-cleared pair can now be heard on the actual finite conventional
tree, preserving the signed scalar left by all earlier integrations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRankedPair
open Function Lattice Wilson PertExtension RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding
open XSpace FVA2 PowerSeries WilsonIndependentMatchedOrbitReading
open scoped Classical BigOperators
variable {G:Gauge}{R:XSpace.Period}(T:R.Tree)

theorem ranked (O:Config G R.side→ℝ)(h:Orb.PreTest O)(admitted:Plan G R.side (insert O))
    (field:Bare.Series T G)(r q:ℕ)
    (printed:PowerSeries.X^r * field = BareOrb.stencil T O):
    coeff q (Bare.normalized T G field)=(plotPT originalClock (insert O) r q:ℂ) := by
  have move (A:Bare.Series T G) :
      PowerSeries.X^r * Bare.normalized T G A =
      Bare.normalized T G (PowerSeries.X^r * A) := by
    rw [←Bare.normalized_scalar]
    simp [Bare.scalar]
  have normalized:=((move field).trans (congrArg (Bare.normalized T G) printed)).trans
    (diagram T O h admitted)
  have head:=congrArg (coeff (r+q)) normalized
  simpa [coeff_X_pow_mul',plotPT,Nat.le_add_right,coeff_mk] using head

/-- Multiplying the actual two cleared stencils precedes the vacuum division.
The group-word product is factored on this very tree. -/
theorem pair (O P:Config G R.side→ℝ)(ho:Orb.PreTest O)(hp:Orb.PreTest P)
    (price:Orb.PreTest (O*P))
    (admitted:Plan G R.side (insert (O*P)))
    {A B:Bare.Series T G}{r s q:ℕ}
    (left:PowerSeries.X^r*A=BareOrb.stencil T O)
    (right:PowerSeries.X^s*B=BareOrb.stencil T P) :
    coeff q (Bare.normalized T G (A*B))=
      (plotPT originalClock (insert (O*P)) (r+s) q:ℂ) := by
  apply ranked T (O*P) price admitted
  rw [pow_add,WilsonOriginalPivotWardProduct.product T ho hp,←left,←right]
  ring

end YM.Integration.WilsonIndependentMatchedRankedPair
end
