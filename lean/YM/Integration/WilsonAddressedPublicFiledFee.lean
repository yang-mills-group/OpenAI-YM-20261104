import YM.Integration.WilsonAddressedPublicSignedFare
import YM.Integration.WilsonReflectedOpticalStock
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFiledFee
open Function Filter Lattice Wilson RG Source Labels
open Extraction Table Spec Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Work.G08
open Next.Foundations OPE.Therm Push.AbsoluteSums.Animals
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonAddressedRestartedColumn WilsonOriginalNullCorridor WilsonPositionProgramOriginalBlockedTrial
open WilsonMeasuredPublicEntranceGridDebit WilsonOriginalMicroscopicGuardedReporters
open WilsonPositionHomogeneousFrame WilsonThermometerUnitFilingFourSquare
open WilsonPositionProgramBlockedPublicExperiment WilsonAddressedPublicPool
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {ord : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family ord S) (l : Ultrafilter (ℕ×ℕ))



open WilsonInvariantActionPosition
local notation "a_" => R.family.S.a
local notation "H_" => R.family.path.levels.clock.hatBeta


open WilsonReflectedAffordableArm
def price (d:ℕ):ℝ:=12+|GermGraph.price (C:=R.family) d| *Real.exp 200

/-- At the actual receiving date a single additional thermal power pays both
    rooted stores and the measured finite coordinate of the same signed row. -/
theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit):
    ∀ᶠ f:ℕ in atTop, (R.family.path.levels.budget f).supportExponent  ≤ 100 →
    ∀d p q (B W:ℝ)(σ:ℂ),0 ≤ B →     ‖σ‖*B  ≤  W*((H_ f)^(q+1))⁻¹ →
    let due:=price R d*W*((H_ f)^q)⁻¹
    ‖σ‖*((1+4*stock R.family f)*B)  ≤  due ∧
    ‖σ‖*((invoice (C:=R.family) d f p+4)*B)  ≤  due ∧
    ‖σ‖*(2*B)  ≤  due:=by
  filter_upwards [WilsonReflectedOpticalStock.columns R simple slow] with f stockfee
  intro exponent d p q B W σ bp earned
  have clock:=R.family.path.levels.fits.delayed f
  have hp:=zero_lt_one.trans clock
  let v:=|GermGraph.price (C:=R.family) d| *Real.exp 200
  have vp:0 ≤ v:=mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have fresh:projectionBill R d f ≤ v:=mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith only [exponent])) (abs_nonneg _)
  have column:0 ≤ stock R.family f:=zero_le_one.trans (R.family.path.levels.params f).columns_ge
  have tariff:0 ≤ price R d:=by change 0 ≤ 12+v;linarith only [vp]
  have head:v ≤ v*H_ f:=le_mul_of_one_le_right vp clock.le
  have enough (c:ℝ)(credit:c  ≤  price R d*H_ f):
      ‖σ‖*(c*B)  ≤  price R d*W*((H_ f)^q)⁻¹:=by
    calc
      _ = c*(‖σ‖*B):=by ring
      _  ≤  (price R d*H_ f)*(W*((H_ f)^(q+1))⁻¹):=
        mul_le_mul credit earned (mul_nonneg (norm_nonneg _) bp) (mul_nonneg tariff hp.le)
      _ = _:=by rw [pow_succ];field_simp [hp.ne']
  refine ⟨enough _ ?_,enough _ ?_,enough _ ?_⟩
  · change 1+4*stock R.family f  ≤  (12+v)*H_ f
    linarith only [stockfee,clock,head,vp]
  · change invoice (C:=R.family) d f p+4  ≤  (12+v)*H_ f
    linarith only [projected R d f p,fresh,clock,head]
  · change 2  ≤  (12+v)*H_ f
    linarith only [clock,head,vp]

end YM.Integration.WilsonAddressedPublicFiledFee
end
