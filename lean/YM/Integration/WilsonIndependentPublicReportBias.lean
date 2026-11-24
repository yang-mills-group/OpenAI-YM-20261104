import YM.Integration.WilsonIndependentPublicReportClock
import YM.WilsonCoeffUV.Vacuum.Step.Ratio
import YM.RegulatorIR.Calibration.Polarity

/-! Express the actual finite report reversion through the native
priced Wilson bias operator. The square-root branch is fixed at one. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentPublicReportBias
open RegulatorIR RegulatorIR.Binding RegulatorIR.Prim RegulatorIR.Clocks RegulatorIR.Clocks.Warp
open RegulatorIR.Profiles RegulatorIR.Calibration PertExtension Series Series.Radial Series.Tested
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank PowerSeries
open WilsonIndependentPublicReportClock
open scoped Classical PowerSeries ContDiff

def beta (K:Feeds):Writing:=tale K.scale.beta

theorem origin (K:Feeds):constantCoeff (beta K)=1:=by
  rw [←coeff_zero_eq_constantCoeff_apply]
  exact RegulatorIR.Calibration.returns _

theorem square (K:Feeds):beta K*(tale K.dine)^2=1:=by
  have smooth:ContDiffAt ℝ ∞ K.scale.beta 0:=(K.smooth.inv (K.positive 0).ne').pow 2
  have pwr:=Script.dictates (K.smooth.pow 2) (Outlook.script_pow (Script.actual K.smooth) 2)
  change tale K.scale.beta*(tale K.dine)^2=1
  rw [←pwr,←tale_mul smooth (K.smooth.pow 2)]
  have one:K.scale.beta*K.dine^2=(fun _:ℝ=>1):=by
    funext x
    change ((K.dine x)⁻¹)^2*(K.dine x)^2=1
    rw [←mul_pow,inv_mul_cancel₀ (K.positive x).ne',one_pow]
  change RegulatorIR.Prim.tale (K.scale.beta*K.dine^2)=1
  rw [one,tale_const,map_one]

theorem forward (K:Feeds):gamma K=oldG (beta K):=by
  let A:=tale K.dine
  have ba:beta K≠0:=by intro h;simpa [h] using origin K
  have sq:A^2=(pace (beta K))^2:=mul_left_cancel₀ ba ((square K).trans (pace_tax (origin K)).symm)
  have top:constantCoeff A=1:=by
    rw [←coeff_zero_eq_constantCoeff_apply]
    exact tale_base.trans K.origin
  have actual:A=pace (beta K):=by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp sq with h|h
    · exact h
    · have mismatch:=congrArg constantCoeff h
      rw [top,map_neg,pace_cc (origin K)] at mismatch
      norm_num at mismatch
  exact (mul_comm _ A).trans (congrArg (fun z:Writing=>z*PowerSeries.X) actual)

/-- The fresh coupling is the actual inverse of the printed report. -/
theorem backward (K:Feeds):inverse K=back (beta K)*PowerSeries.X:=by
  rw [fresh_back]
  have h:PowerSeries.subst (freshG (beta K)) (gamma K)=PowerSeries.X:=by
    rw [forward K];exact reverse_right (origin K)
  have h0:coeff 0 (freshG (beta K))=0:=(coeff_zero_eq_constantCoeff_apply _).trans (fresh_coeff _)
  have p:=composed h0 (gamma_s K) (inverse K)
  have q:(inverse K).subst (gamma K)=PowerSeries.X:=(poses K).strongP
  rw [q,PowerSeries.subst_X (permits h0),h,PowerSeries.X_subst] at p
  exact p.symm

theorem restoring (K:Feeds):factor K=(back (beta K))⁻¹:=by
  have charge:=units K
  rw [backward K] at charge
  have hx:(PowerSeries.X:Writing)≠0:=PowerSeries.X_ne_zero
  have cost:back (beta K)*factor K=1:=by
    apply mul_left_cancel₀ hx
    calc PowerSeries.X*(back (beta K)*factor K)=(back (beta K)*PowerSeries.X)*factor K:=by ring
         _=PowerSeries.X*1:=by rw [charge,mul_one]
  have hn:back (beta K)≠0:=by
    intro h
    have unit:=back_cc (origin K)
    rw [h,map_zero] at unit
    exact zero_ne_one unit
  exact mul_left_cancel₀ hn (cost.trans (PowerSeries.mul_inv_cancel (back (beta K))
    (by rw [back_cc (origin K)];simp)).symm)

end YM.Integration.WilsonIndependentPublicReportBias
