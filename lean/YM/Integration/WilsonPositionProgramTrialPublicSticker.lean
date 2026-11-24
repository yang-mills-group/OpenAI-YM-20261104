import YM.Integration.WilsonPositionProgramTrialPublicHome
import YM.Integration.WilsonOriginalPublicNodalPlainSensor
import YM.Integration.WilsonIndependentMatchedOpeningFiled

/-! The group words used by the observed pairs at their real roots, contracted with the
actual numerical paid K vector. The equality holds in the complete cover algebra. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicSticker
open Function Finset PowerSeries Lattice RG Wilson Tree Source Labels XSpace XSpace.Rose
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Power WilsonCoeffUV.Bank
open WilsonCoeffUV.Soil WilsonCoeffUV.Shard WilsonCoeffUV.Wheel.Mark
open WilsonOriginalPublicNodalPlainSensor (sensor)
open WilsonIndependentMatchedOpeningRoster (seat)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentMatchedOpeningFiled (planted terms)
open WilsonOriginalPhysicalFruitVerse (written)
open WilsonPositionProgramSubmittedCoordinates (plain)
open scoped Classical BigOperators
variable {G:Gauge}{d D:ℕ}(R:Run G)(W:Initialize G)(cut:d<D)
local notation "F" => R.family.labels.level d

private theorem empty (Y:Era G ℝ):affiled 0 Y=0:=by
  apply Prod.ext
  · funext n j l x
    simp [affiled,affix]
  · funext j l x
    simp [affiled,affix]

def paidWord (b:Volume D)(v:(F).Coeff)(φ:ℂ→L[ℝ]ℝ)(o:Cover):Era G ℝ:=
  ∑j:(F).Index,affiled (PowerSeries.C (φ (v j))*
    (PowerSeries.C (sensor D b)*(PowerSeries.X:Cost)^((F).grades j).2))
    (column R W false cut (seat (F) j) o)

theorem original (b:Volume D)(v:(F).Coeff)(φ:ℂ→L[ℝ]ℝ)(o:Cover):
    planted R W false cut b (written (F) v φ) o=paidWord R W cut b v φ o:=by
  rw [WilsonIndependentMatchedOpeningFiled.original]
  unfold paidWord
  refine (WilsonOriginalPublicNodalPlainSensor.compress (F) _ ?_).trans ?_
  · intro s hs
    change affiled (written (F) v φ s*PowerSeries.C _) _=0
    simp only [written,if_neg hs,zero_mul]
    exact empty _
  · apply Finset.sum_congr rfl
    intro j _
    unfold terms WilsonIndependentMatchedTopReceipt.realDose
    apply congrArg (fun c=>affiled c (column R W false cut (seat (F) j) o))
    rw [WilsonOriginalPublicNodalPlainSensor.chosen]
    have native:written (F) v φ (WilsonPositionProgramSubmittedCoordinates.plain (F) j)=
        PowerSeries.monomial (((F).grades j).2) (φ (v j)):=by
      simp [written,WilsonPositionProgramSubmittedCoordinates.plain,rankS,valence,sheet]
    have power (l:ℕ)(a:ℝ):(PowerSeries.monomial l a:Cost)=PowerSeries.C a*PowerSeries.X^l:=by
      ext n
      rw [coeff_monomial,coeff_C_mul,coeff_X_pow]
      split_ifs <;> simp_all
    rw [native,power]
    ring

theorem registered {N per K:ℕ}(b:Volume D)(r:ℝ)(t:ℂ)(φ:ℂ→L[ℝ]ℝ)(v:R.family.label d)(o:Cover):
    planted R W false cut b (WilsonPositionProgramTrialPublicHome.label R N per K r t φ v) o=
      paidWord R W cut b (WilsonOriginalPhysicalFruitDose.amounts R d K N per r t v) φ o:=
  original R W cut b _ φ o

end YM.Integration.WilsonPositionProgramTrialPublicSticker
end
