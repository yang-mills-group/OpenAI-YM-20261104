import YM.RegulatorIR.Clocks.Test
import YM.RegulatorIR.Calibration.Upright

/-! Reporting coordinates on one finite Notebook. Clear every Laurent
dose in the original variable before substituting the report clock.
The measured Rose subsequently removes this temporary clock. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentPublicReportClock
open RegulatorIR RegulatorIR.Clocks RegulatorIR.Profiles RegulatorIR.Prim
open PertExtension Series Series.Radial Series.Tested RegulatorIR.Geometry RegulatorIR.Calibration
open PowerSeries RegulatorIR.Clocks.Warp
open scoped Classical PowerSeries

abbrev inverse (K:Feeds):Writing:=(poses K).invertU
abbrev factor (K:Feeds):Writing:=(tale K.dine).subst (inverse K)
def cleared (K:Feeds)(D:ℕ)(A:Writing):Writing:=(factor K)^D*A.subst (inverse K)
def relative (K J:Feeds):Writing:=(gamma J).subst (inverse K)

theorem units (K:Feeds):inverse K*factor K=PowerSeries.X:=by
  have h: (gamma K).subst (inverse K)=PowerSeries.X:=(poses K).strongI
  rw [gamma,PowerSeries.subst_mul (permits (poses K).ready),
    PowerSeries.subst_X (permits (poses K).ready)] at h
  exact h

/-- The restoring unit is determined by the actual report on this board. -/
theorem pole (K:Feeds)(D:ℕ)(A:Writing):
    (inverse K)^D*cleared K D A=PowerSeries.X^D*A.subst (inverse K):=by
  unfold cleared
  rw [←mul_assoc,←mul_pow,units]

/-- The relative stop clock acts on all the coefficients of the stopped
word, including its previously deposited unit. -/
theorem stopped (K J:Feeds)(D:ℕ)(F:Writing):
    cleared K D (F.subst (gamma J))=(factor K)^D*F.subst (relative K J):=by
  exact congrArg (fun T=>(factor K)^D*T) (composed (poses K).ready (gamma_s J) F)

/-- The same report transformation occurs on the fitted target and on
the centered, normalized Rose. The finite constant is held separately. -/
theorem rose (K:Feeds)(R:Reset)(Z:Writing):
    let s:Writing:=inverse K
    let reverse:Writing:=PowerSeries.subst R.invertU (gamma K)
    PowerSeries.subst reverse (PowerSeries.subst s R.bill)=PowerSeries.X ∧
      PowerSeries.subst (PowerSeries.subst s R.bill) reverse=PowerSeries.X ∧
      PowerSeries.subst reverse (PowerSeries.subst s Z)=Z.subst R.invertU:=by
  intro s reverse
  have shifted (V:Writing):
      PowerSeries.subst reverse (PowerSeries.subst s V)=V.subst R.invertU:=by
    change PowerSeries.subst ((gamma K).subst R.invertU) (V.subst (poses K).invertU)=_
    rw [←composed R.ready (gamma_s K) (V.subst s)]
    exact congrArg (PowerSeries.subst R.invertU) ((poses K).introduces V)
  have other (V:Writing):
      PowerSeries.subst (PowerSeries.subst s R.bill) (PowerSeries.subst R.invertU V)=V.subst s:=by
    rw [←composed (poses K).ready R.signal (V.subst R.invertU),R.introduces V]
  exact ⟨(shifted R.bill).trans R.strongI,(other (gamma K)).trans (poses K).strongI,shifted Z⟩

end YM.Integration.WilsonIndependentPublicReportClock
