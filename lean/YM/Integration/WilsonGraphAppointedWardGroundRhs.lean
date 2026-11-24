import YM.Integration.WilsonGraphAppointedWardGroundMatrix
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentGroupFirstWardTree

set_option autoImplicit false

noncomputable section

namespace YM.Integration.WilsonGraphAppointedWardGroundRhs

open _root_.YangMills _root_.YangMills.Matching
open _root_.PhysicalMatching.H7StandaloneFourSmearedWardReadings (Pupils probes)
open _root_.PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients (rhsCoefficients)
open WilsonGraphStandaloneCorrelation (Label)
open MeasureTheory
open scoped Classical BigOperators

variable {g : GaugeGroup} {H : g.core.Simple}

/-- The translation source on the two original magnetic probes. -/
def maxwellRhs (H : g.core.Simple) (P : Pupils) : Fin 4 → ℂ :=
  ![0, 0, 0, -(∫ x : Points 2, Ward.firstDerivative 0 (fun y => P.translation y) x *
    (maxwellReference g).moment x (fun _ : Fin 2 => (probes H 0).val))]

theorem atPupils (Z : _root_.YM.FVA2.Register.WilsonPrescription g.core)
    (Q : _root_.YM.Answer.ContinuumLimit.Perspective H Z true) (P : Pupils) :
    rhsCoefficients Z Q P 0 = maxwellRhs H P := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · apply congrArg Neg.neg
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases h : Ward.firstDerivative 0 (fun y => P.translation y) x = 0
    · simp [h]
    · have hx : x ∈ separated 2 :=
        (_root_.PhysicalMatching.H7StandaloneSmearedWardMatrixExpansion.derivativeWeight
          P.translation 0).2.2 (subset_tsupport _ h)
      let S := _root_.IssuedBridge.PostedAppointedConversion.filed Z Q.MS Q.matching
        (_root_.YM.FVA2.Teller.logNu 1)
      let a : Fin 2 → Label g := fun _ => ⟨4, probes H 0⟩
      exact congrArg (fun z : ℂ => Ward.firstDerivative 0 (fun y => P.translation y) x * z)
        ((WilsonGraphAppointedWardGroundMatrix.converted S 0 a x hx).trans
          (_root_.PhysicalMatching.H7IndependentGroupFirstWardTree.groupLeading S a x hx))

end YM.Integration.WilsonGraphAppointedWardGroundRhs

end

