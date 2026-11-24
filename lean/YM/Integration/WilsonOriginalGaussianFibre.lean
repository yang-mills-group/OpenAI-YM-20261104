import YM.Integration.WilsonOriginalRegisteredRawPage

/-! The enrolled Gaussian and real exterior colour coordinates before the Wick contraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGaussianFibre
open Function Finset Marker Multi Laurent Bloch Wilson RG Precision Lattice Tree Matrix Exterior
open PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Cumulants FreeResolvent
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay WilsonVacuumPreResetDepositedGeometric
open scoped Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio)(B:fieldDir G c 1)

theorem coordinates (z:Precision.Key F G→ℝ):
    SignedRegisteredKernelPolynomial.focus F B z = Sum.elim z (flatten B) :=by
  funext a
  cases a with
  | inl a=>rfl
  | inr a=>rfl

theorem reading (P:MvPolynomial (Active G F⊕Woods G c) ℝ)(z:Precision.Key F G→ℝ):
    Cloud.paint z (SignedRegisteredMarkedProgram.register F B P)=
      (MvPolynomial.eval (Sum.elim z (flatten B)) P:ℝ):=by
  rw [SignedRegisteredMarkedProgram.reading,coordinates]

end YM.Integration.WilsonOriginalGaussianFibre
