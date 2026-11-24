import YM.Integration.WilsonGraphAppointedWardTranslationRow
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentFiledMaxwellWardAction

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGraphAppointedWardGroundVector

open _root_.YangMills
open _root_.PhysicalMatching.H7StandaloneFourSmearedWardReadings (Pupils)
open _root_.PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients (matrixCoefficients rhsCoefficients)
open _root_.PhysicalMatching.H7StandaloneFiniteWardMatrix (act)
open _root_.PhysicalMatching.H7IndependentFourMaxwellWardReadings (leading)
open scoped BigOperators

private theorem fourthColumn (L : Matrix (Fin 4) (Fin 4) ℂ) (i : Fin 4) :
    act L (![0, 0, 0, 1] : Fin 4 → ℂ) i = L i 3 := by
  change (∑ j : Fin 4, L i j * (![0, 0, 0, 1] : Fin 4 → ℂ) j) = L i 3
  simp [Fin.sum_univ_succ]

variable {g : GaugeGroup} {H : g.core.Simple}
variable (Z : _root_.YM.FVA2.Register.WilsonPrescription g.core)
variable (Q : _root_.YM.Answer.ContinuumLimit.Perspective H Z true) (P : Pupils)
local notation "L₀" => matrixCoefficients Z Q P 0

/-- The independent ground equation on the original four tested rows. -/
theorem atPupils (rows : ∀ i j, L₀ i j = leading (L₀ 3 1) (L₀ 3 2) i j) :
    rhsCoefficients Z Q P 0 = act L₀ ![0, 0, 0, 1] := by
  funext i
  rw [fourthColumn]
  fin_cases i
  · exact (rows 0 3).symm
  · exact (rows 1 3).symm
  · exact (rows 2 3).symm
  · exact (WilsonGraphAppointedWardTranslationRow.atPupils Z Q P).symm

end YM.Integration.WilsonGraphAppointedWardGroundVector
end

