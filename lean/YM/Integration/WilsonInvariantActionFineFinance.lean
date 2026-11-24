import YM.Integration.WilsonInvariantActionFineCurvature
import YM.Integration.WilsonInvariantActionFineReserve

/-! All fixed moments of the restored curvature discrepancy in the original measured fine law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionFineFinance
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Shoot Marker OPE.Therm Comparison.RG02
open Comparison.Density.RenderM Comparison.Density.RenderM.Token ActualRunPacketRetuning
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Pert.Asymptotics
open ManuscriptQLocalOriginalConditionalTail ManuscriptQLocalRegularConditional ManuscriptQLocalSourceFourier
open RG.Supply Next.Rank Push.GridApprox WardBin.Wheels
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Scheduling Next.Scheduling.Clock
open Push.PriceCompiler Next.Foundations Source RG3.Script.Picnic PhysicalNext.ThroughLaunch WilsonLimitConstruction
open Actual Order IterationFour IterationFour.Vacuum
open WilsonInvariantActionTransportedOld WilsonInvariantActionMixedMaterial
open RG16 PertExtension Tree Precision RG17 RG12 Extraction Spec OPE Table SharpGram.Lenses Pier.Lair Overlay PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
open MergeProof.Accent

open ActualOriginalQCharges ActualOriginalQPackets ActualOriginalQReaders

open MS.Local.Physical Finset
open WilsonMatrixOriginalIndependentFields WilsonMatrixOriginalCurvatureStock WilsonMatrixOriginalCurvatureField
open WilsonMatrixTicketLanesReportedPivot WilsonReportingPrescribedOldWardWallet


open WilsonInvariantActionCurvatureFrame WilsonMatrixOriginalIndependentColumns WilsonMatrixTicketLanesNativePrices


open private payroll from YM.Integration.WilsonInvariantActionCurvatureReturn
open WilsonInvariantActionFineCurvature
variable {G:Gauge} {B:Deck G} (R:Run G) (simple:G.Simple) (Q:MS.Land.Prescription B)
local notation "slots" => B.BIndex (4:ℤ) 2
local notation "sources" => WilsonReportingPrescribedOldAction.label B
variable (J:Request (B.BIndex (4:ℤ) 2)) (A:NumericSchedule R.family J) (μ:ℝ)
variable {f:Extraction.Order} {S:Table R.family.book} (Φ:Spec.Final R.family f S) (L:RG17.Layout Φ)
  (U:Ultrafilter (ℕ×ℕ)) (cut:(U:Filter (ℕ×ℕ)) ≤ L.lens)

private theorem redeem {Ω:Type*} [MeasurableSpace Ω] (ν:Measure Ω) (D:Ω→ℂ) (hD:Measurable D)
    (R₀:Ω→ℝ) (p:ℕ) {s a b:ℝ} (hs:0 ≤ s) (ha:0 ≤ a) (h:∀T,0 ≤ R₀ T ∧ ‖D T‖ ≤ s*R₀ T)
    (paid:Integrable (fun T=>(R₀ T)^(p+1)) ν ∧ (∫T,(R₀ T)^(p+1) ∂ν) ≤ a^(p+1))
    (price:s*a ≤ b):
    Integrable (fun T=>‖D T‖^(p+1)) ν ∧ (∫T,‖D T‖^(p+1) ∂ν) ≤ b^(p+1):=by
  have cap T:‖D T‖^(p+1) ≤ s^(p+1)*(R₀ T)^(p+1):=by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h T).2 _
  have funded:Integrable (fun T=>s^(p+1)*(R₀ T)^(p+1)) ν:=paid.1.const_mul _
  have valid:Integrable (fun T=>‖D T‖^(p+1)) ν:=funded.mono'
    (hD.norm.pow_const _).aestronglyMeasurable (ae_of_all _ fun T=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)];exact cap T)
  refine ⟨valid,(integral_mono valid funded cap).trans ?_⟩
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left paid.2 (pow_nonneg hs _)).trans ?_
  rw [←mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg hs ha) price _

theorem measurable (d:LocalFormal.Datum R.family (Stock.census (B.BIndex (4:ℤ) 2)))
    (v:R.family.label 4) (o:Site (R.family.side (d.level+1) d.period))
    (age:R.family.ref 4 ≤ d.level+1):
    Measurable (fun T=>R.family.O (d.level+1) d.period (center R (d.level+1) d.cutoff d.period v) o T-
      masked R simple J A Q μ d v o T):=by
  let u:=WilsonReportingPrescribedOldAction.label B
  let z:=WilsonMatrixTicketLanesSelectedNormalization.stamp R μ d
  let x:=unitTest (B:=B) R J
  let P:=ActualOriginalQInitialInput.packets R simple u J A d Q (fun _=>o) z (fun _=>0)
  let g:=regulatorRun R.family d.cutoff d.period (d.level+1)
  have X:=ManuscriptQLocalOriginalFineMaskLoss.full_borel P x (g:=g)
  have Y:=ManuscriptQLocalOriginalFineMaskLoss.mask_borel P x (R.family.path.rep d.cutoff d.period (d.level+1)).p (g:=g)
  have change:Measurable (deficit R simple J A Q μ d o):=X.sub Y
  simp_rw [difference R simple J A Q μ d v o age]
  exact Finset.measurable_fun_sum _ fun i _=>measurable_const.mul
    ((Poly.get ((Stock.census slots).fire i)).continuous.measurable.comp change)

include cut in
theorem original (warm:Poetry R.family.path.levels) (e p q:ℕ) {ε:ℝ} (hp:0<ε):
    ∀ᶠ m:ℕ in atTop,∀(d:LocalFormal.Datum R.family (Stock.census (B.BIndex (4:ℤ) 2))),d.level=m →
      ∀(v:R.family.label 4) (o:Site (R.family.side (d.level+1) d.period)) (M:ℝ), 0 ≤ M →
      R.family.ref 4 ≤ d.level+1 →
      (R.family.S.a (d.level+1)^4)⁻¹*Next.UVStress.quota R.family 4 (d.level+1) d.cutoff d.period v ≤ 
        R.family.path.levels.clock.hatBeta (d.level+1)^e*M →
      let ν:=scene R.family.path d.cutoff d.period (d.level+1)
      let g:=regulatorRun R.family d.cutoff d.period (d.level+1)
      let loss:=fun T=>‖R.family.O (d.level+1) d.period (center R (d.level+1) d.cutoff d.period v) o T-
        masked R simple J A Q μ d v o T‖^(p+1)
      Integrable loss ν ∧ (∫T,loss T ∂ν) ≤ (ε*g^q*M)^(p+1):=by
  classical
  let C:=1+8*fare (warehouse R) B 4*(2:ℝ)^(e+1)
  have hd:0 ≤ fare (warehouse R) B 4:=sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _
  have hc:0<C:=by dsimp only [C];positivity
  by_cases available:Nonempty slots
  · letI:=available
    have funds:=WilsonInvariantActionFineReserve.original R simple (sources) J A Q warm μ 0 p
      ((q+2*(e+1))*(p+1)) (pow_pos (div_pos hp hc) (p+1))
    filter_upwards [funds] with m income
    intro d md v o M hM age bill ν g loss
    let z:=WilsonMatrixTicketLanesSelectedNormalization.stamp R μ d
    let H:=ActualOriginalQInitialInput.normalizer R simple (sources) J A d Q (fun _=>o) z (fun _=>0)
    let w:=fun T=>H*Poly.price (fun _:slots=>1) (deficit R simple J A Q μ d o T)
    let y:=stock B (amounts R B (d.level+1) d.period (center R (d.level+1) d.cutoff d.period v))
    let mass:=∑i,‖normalization R (d.level+1)*y.2 i‖
    have hH:0 ≤ H:=zero_le_one.trans (le_max_left _ _)
    have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson d.below))
    have receipt:=income d md (fun _=>o) (fun _=>0) (fun _=>le_rfl) (unitTest (B:=B) R J)
    change Integrable (fun T=>(w T)^(p+1)) ν ∧
      (∫T,(w T)^(p+1) ∂ν) ≤ (ε/C)^(p+1)*g^((q+2*(e+1))*(p+1)) at receipt
    rw [pow_mul,←mul_pow] at receipt
    have cap(T:_):0 ≤ w T ∧ ‖R.family.O (d.level+1) d.period (center R (d.level+1) d.cutoff d.period v) o T-
        masked R simple J A Q μ d v o T‖ ≤ mass*w T:=by
      refine ⟨mul_nonneg hH (Poly.nonnegative (fun _:slots=>zero_lt_one) _),?_⟩
      exact (gross R simple J A Q μ d v o age T).trans_eq (mul_assoc _ _ _)
    have debit:=payroll (B:=B) R Φ L U cut (d.level+1) d.cutoff d.period d.below v e q hp hM
      (show (0:ℝ) ≤ 1 by norm_num) bill
    simp only [mul_one] at debit
    exact redeem ν _ (measurable R simple Q J A μ d v o age) w p
      (sum_nonneg fun _ _=>norm_nonneg _) (mul_nonneg (div_pos hp hc).le (pow_nonneg gp.le _))
      cap receipt debit
  · letI:IsEmpty slots:=not_nonempty_iff.mp available
    filter_upwards [] with m
    intro d _ v o M hM age _ ν g loss
    have zeroT(T:_):R.family.O (d.level+1) d.period (center R (d.level+1) d.cutoff d.period v) o T-
        masked R simple J A Q μ d v o T=0:=(difference R simple J A Q μ d v o age T).trans (by simp)
    have zeroLoss:loss=fun _=>0:=funext fun T=>by simp [loss,zeroT]
    rw [zeroLoss]
    have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson d.below))
    letI:IsProbabilityMeasure ν:=probability R.makes.wilson d.below
    refine ⟨integrable_const 0,?_⟩
    rw [integral_zero]
    exact pow_nonneg (mul_nonneg (mul_nonneg hp.le (pow_nonneg gp.le _)) hM) _

end YM.Integration.WilsonInvariantActionFineFinance
