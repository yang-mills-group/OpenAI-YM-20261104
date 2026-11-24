import YM.Integration.WilsonOriginalMicroscopicEntrancePeerFare
import YM.Integration.WilsonOriginalMicroscopicEntranceGridCensus

/-! Cancellation of the actual physical engineering scale at the f-ear.
The source-receiver stock and the two separate real lamp portfolios retain
their native tariffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntrancePeerRefund
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent Marker
open WilsonReflectedAffordableArm (charge projected projectionBill)
open WilsonOriginalCompanionLowerPeer (tariff)
open WilsonMeasuredCompanionSoft (expense)
open WilsonOriginalMicroscopicEntranceGridRow (factor)
open Pert.Asymptotics
open scoped Classical
variable {G:Gauge}(R:Run G)
local notation "CF" => R.family

theorem original (d N p f q:ℕ)(v:Fin 3)(H V w:ℝ)(F:ℂ)(pos:0≤H)
    (salary:charge R d f*H≤(R.family.S.a f)^d*V)
    (bill:w*‖F‖≤‖factor R (fun _=>d) f v‖*(
      WilsonOriginalCompanionLowerPeer.tariff*((1+4*stock CF f)*H)*(regulatorRun CF N p f)^q+
      (|WilsonThermometerUnitFilingFieldRange.cost G d ((CF).path.rep N p f).p.threshold| *((invoice (C:=CF) d f p+4)*H)+(1+4*stock CF f)*H)*WilsonMeasuredCompanionSoft.expense 1)):
    w*‖F‖≤V*(|WilsonOriginalCompanionLowerPeer.tariff| *(regulatorRun CF N p f)^q+
      (|WilsonThermometerUnitFilingFieldRange.cost G d ((CF).path.rep N p f).p.threshold|+1)*WilsonMeasuredCompanionSoft.expense 1):=by
  let af:=(CF).S.a f
  let c:=|WilsonThermometerUnitFilingFieldRange.cost G d ((CF).path.rep N p f).p.threshold|
  have cp:0≤c:=abs_nonneg _
  have ap:0<af:=(CF).S.a_pos f
  have phi:0<af^d:=pow_pos ap d
  have st:0 ≤ stock CF f:=zero_le_one.trans (((CF).path.levels.params f).columns_ge)
  have pr:0≤projectionBill R d f:=mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have b0:0≤(1+4*stock CF f)*H:=mul_nonneg (by linarith only [st]) pos
  have b: (1+4*stock CF f)*H≤af^d*V:=by
    apply le_trans _ salary
    exact mul_le_mul_of_nonneg_right (by unfold WilsonReflectedAffordableArm.charge;linarith only [pr]) pos
  have i:(invoice (C:=CF) d f p+4)*H≤af^d*V:=by
    apply le_trans _ salary
    exact mul_le_mul_of_nonneg_right (by unfold WilsonReflectedAffordableArm.charge;linarith only [st,projected R d f p]) pos
  have g:0≤(regulatorRun CF N p f)^q:=pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _
  have ep:0≤WilsonMeasuredCompanionSoft.expense 1:=by unfold WilsonMeasuredCompanionSoft.expense;positivity
  have spatial:‖WilsonOriginalMicroscopicEntranceGridRow.factor R (fun _=>d) f v‖=(af^d)⁻¹:=by
    simp [WilsonOriginalMicroscopicEntranceGridRow.factor,af,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ((CF).S.a_pos f)]
  rw [spatial] at bill
  apply bill.trans
  calc
    (af^d)⁻¹*(WilsonOriginalCompanionLowerPeer.tariff*((1+4*stock CF f)*H)*(regulatorRun CF N p f)^q+
        (c*((invoice (C:=CF) d f p+4)*H)+(1+4*stock CF f)*H)*WilsonMeasuredCompanionSoft.expense 1) ≤
      (af^d)⁻¹*(|WilsonOriginalCompanionLowerPeer.tariff| *(af^d*V)*(regulatorRun CF N p f)^q+(c*(af^d*V)+af^d*V)*WilsonMeasuredCompanionSoft.expense 1):=by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr phi.le)
      apply add_le_add (mul_le_mul_of_nonneg_right _ g)
        (mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left i cp) b) ep)
      exact (mul_le_mul_of_nonneg_right (le_abs_self WilsonOriginalCompanionLowerPeer.tariff) b0).trans (mul_le_mul_of_nonneg_left b (abs_nonneg _))
    _ = V*(|WilsonOriginalCompanionLowerPeer.tariff| *(regulatorRun CF N p f)^q+(c+1)*WilsonMeasuredCompanionSoft.expense 1):=by
      field_simp [phi.ne']

end YM.Integration.WilsonOriginalMicroscopicEntrancePeerRefund
end
