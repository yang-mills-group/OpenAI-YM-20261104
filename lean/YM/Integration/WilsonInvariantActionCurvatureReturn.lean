import YM.Integration.WilsonInvariantActionCurvatureFrame
import YM.Integration.WilsonMatrixTicketLanesRegisteredLoss

/-! The prescribed retained curvature columns against the genuine signed earlier Wilson insertion. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionCurvatureReturn
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

variable {G:Gauge} {B:Deck G} (R:Run G) (simple:G.Simple) (Q:MS.Land.Prescription B)
local notation "slots" => B.BIndex (4:ℤ) 2
local notation "basis₀" => WilsonReportingPrescribedOldAction.label B
variable (J:Request (B.BIndex (4:ℤ) 2)) (A:NumericSchedule R.family J) (τ:ℝ)
variable {f:Extraction.Order} {S:Table R.family.book} (Φ:Spec.Final R.family f S) (L:RG17.Layout Φ)
  (E:OPE.Services R.family f S) (U:Ultrafilter (ℕ×ℕ)) (cut:(U:Filter (ℕ×ℕ))≤L.lens)
local notation "target₀" => ActualOriginalQPointSetup.request R (basis₀) J

def submitted (d:LocalFormal.Datum R.family (Stock.census (B.BIndex (4:ℤ) 2)))
    (o:Site (R.family.side (d.level+1) d.period))
    (stages:WithStage R.metals.p OriginalRunConstruction.originalOrders)
    (first:ActualOriginalQInitialPreparation.start R simple (basis₀) J A stages≤d.level)
    (period:(ActualOriginalQPointSetup.request R (basis₀) J).physicalPeriodLower≤(R.family.S.period d.period).val)
    (i:slots) (V:Config G (R.family.side d.level d.period)):ℂ:=
  let strength:=τ+R.family.S.scale d.cutoff
  let F:=ActualOriginalQInitialPreparation.analyticInput R simple (basis₀) J A d Q (fun _=>o) strength
    (fun _=>0) stages first period
  let γ:=regulatorRun R.family d.cutoff d.period (d.level+1)
  let price:=ActualOriginalQInitialInput.normalizer R simple (basis₀) J A d Q (fun _=>o) strength (fun _=>0)
  let P:=(R.family.path.rep d.cutoff d.period (d.level+1)).p
  let Y:=ManuscriptQLocalOriginalConditionalTail.source F.packets P γ (WilsonOriginalPointModes.unit (target₀).tests) 1
  (price:ℂ)*(ManuscriptQLocalMeasuredMarkTransport.logarithm R.family (N:=d.cutoff) Y V).part ((Stock.census _).fire i)

private theorem distribute {I:Type*} [Fintype I] (a s t:ℂ) (z f g c:I→ℂ):
    ((a+s*∑i,z i*(f i-c i))-(a+s*∑i,z i*(g i-c i)))*t=∑i,(s*z i)*((f i-g i)*t):=by
  rw [add_sub_add_left_eq_sub,←mul_sub,←sum_sub_distrib,mul_sum,sum_mul]
  exact sum_congr rfl fun i _=>by ring

private theorem jordan {Ω I:Type*} [MeasurableSpace Ω] (ν:Measure Ω) [Fintype I] (a:I→ℂ) (F:I→Ω→ℂ)
    {t:ℝ} (income:∀i,Integrable (F i) ν ∧ (∫V,‖F i V‖ ∂ν)≤t):
    Integrable (fun V=>∑i,a i*F i V) ν ∧
      (∫V,‖∑i,a i*F i V‖ ∂ν)≤(∑i,‖a i‖)*t:=by
  have prod(i:I):Integrable (fun V=>a i*F i V) ν:=(income i).1.const_mul _
  refine ⟨integrable_finsetSum _ (fun i _=>prod i),?_⟩
  calc
    _≤∫V,∑i,‖a i*F i V‖ ∂ν:=integral_mono
      (integrable_finsetSum _ (fun i _=>prod i)).norm (integrable_finsetSum _ fun i _=>(prod i).norm) fun _=>norm_sum_le ..
    _=∑i,‖a i‖*(∫V,‖F i V‖ ∂ν):=by rw [integral_finsetSum _ (fun i _=>(prod i).norm)];simp only [norm_mul,integral_const_mul]
    _≤∑i,‖a i‖*t:=sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (income i).2 (norm_nonneg _)
    _=_:=(sum_mul ..).symm

include cut in
private theorem payroll (k N p:ℕ) (live:k≤N) (v:R.family.label 4) (e q:ℕ) {M b ε:ℝ}
    (hp:0<ε) (hm:0≤M) (hb:0≤b)
    (paid:(R.family.S.a k^4)⁻¹*Next.UVStress.quota R.family 4 k N p v≤R.family.path.levels.clock.hatBeta k^e*M):
    let z:=stock B (amounts R B k p (center R k N p v))
    let g:=regulatorRun R.family N p k
    let C:=1+8*fare (warehouse R) B 4*(2:ℝ)^(e+1)
    (∑i,‖normalization R k*z.2 i‖)*((ε/C)*g^(q+2*(e+1))*b) ≤ε*g^q*M*b:=by
  intro z g C
  let β:=R.family.path.levels.clock.hatBeta k
  let D:=fare (warehouse R) B 4
  have hd:0≤D:=sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _
  have hβ:0≤β:=zero_le_one.trans ((R.family.path.levels.fits.delayed k).le)
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))
  have cp:0<C:=by change 0<1+8*D*(2:ℝ)^(e+1);positivity
  have base:(8*D*(2:ℝ)^(e+1))*(ε/C)≤ε:=by
    calc
      _≤C*(ε/C):=mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (div_pos hp cp).le
      _=_:=by field_simp
  obtain ⟨theta,climate⟩:=WilsonMatrixTicketLanesReportedMaster.units R (f:=f) U (cut.trans L.certified)
  have actual:=WilsonMatrixOriginalGermEntryTariff.funded R B L U cut theta climate k N p v paid
  have scale:‖normalization R k‖=((R.family.path.levels.clock.threshold k)^2)⁻¹*(R.family.S.a k^4)⁻¹:=by
    unfold normalization
    rw [norm_mul,norm_inv,norm_pow,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg (R.family.S.a_pos k).le,Real.norm_of_nonneg (sq_nonneg _),inv_pow,mul_comm]
  have tariff:(∑i,‖normalization R k*z.2 i‖)≤8*β*(β^e*M*D):=by
    simpa only [norm_mul,←mul_sum,scale] using actual
  have power:β^(e+1)*g^(2*(e+1))≤(2:ℝ)^(e+1):=
    (le_div_iff₀ (pow_pos gp _)).mp (WilsonMatrixTicketLanesRegisteredLoss.cutoff R live (e+1))
  calc
    _≤(8*β*(β^e*M*D))*((ε/C)*g^(q+2*(e+1))*b):=mul_le_mul_of_nonneg_right tariff (by positivity)
    _=(8*D*(ε/C)*g^q*M*b)*(β^(e+1)*g^(2*(e+1))):=by rw [pow_add,pow_succ];ring
    _≤(8*D*(ε/C)*g^q*M*b)*(2:ℝ)^(e+1):=mul_le_mul_of_nonneg_left power (by positivity)
    _=(8*D*(2:ℝ)^(e+1)*(ε/C))*g^q*M*b:=by ring
    _≤ε*g^q*M*b:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right base (pow_nonneg gp.le _)) hm) hb

set_option backward.isDefEq.respectTransparency false in
include E cut in
theorem original (warm:Poetry R.family.path.levels)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (q e h H:ℕ) {ε:ℝ} (positive:0<ε):
    ∀ᶠm:ℕ in atTop,∀(d:LocalFormal.Datum R.family (Stock.census (B.BIndex (4:ℤ) 2))),d.level=m→
    ∀(o:Site (R.family.side (d.level+1) d.period))
      (stages:WithStage R.metals.p OriginalRunConstruction.originalOrders)
      (first:ActualOriginalQInitialPreparation.start R simple (basis₀) J A stages≤d.level)
      (period:(ActualOriginalQPointSetup.request R (basis₀) J).physicalPeriodLower≤(R.family.S.period d.period).val)
      (v:R.family.label 4) (P:ℝ),0≤P→
      (R.family.S.a (d.level+1)^4)⁻¹*Next.UVStress.quota R.family 4 (d.level+1) d.cutoff d.period v≤
        R.family.path.levels.clock.hatBeta (d.level+1)^e*P→
    ∀(r:ℝ) (w:R.family.label 4) (M:ℝ),0≤M→ R.family.ref 4≤L.level r→L.level r≤d.level+1 →
      R.family.S.a (L.level r)/R.family.S.a (d.level+1)≤R.family.path.levels.clock.hatBeta (d.level+1)^H →
      mass R.family 4 (L.shift 4 r w)≤R.family.path.levels.clock.hatBeta (L.level r)^h*M →
      ∀(y:Site (R.family.side (d.level+1) d.period)) (I:Set ℕ),
        let γ:=regulatorRun R.family d.cutoff d.period (d.level+1)
        let a:=R.family.O (d.level+1) d.period (center R (d.level+1) d.cutoff d.period v) o
        let b:=centered R (Nat.le_succ _) d.below (RG17.atRef L 4 r (d.cutoff,d.period) w) y I
        let predicted:=fun V=>assembled R Q τ d v o (fun i=>submitted R simple Q J A τ d o stages first period i V)
        let joint:=fun V=>(actualAverage R.family (N:=d.cutoff) a V-predicted V)*b V
        let ν:=scene R.family.path d.cutoff d.period d.level
        Integrable joint ν ∧ (∫V,‖joint V‖ ∂ν)≤ε*γ^q*P*M ∧
          ∀(j:ℕ) (past:j≤d.level),(∫W,‖actualTransport R.family (N:=d.cutoff) joint past W‖
            ∂scene R.family.path d.cutoff d.period j)≤ε*γ^q*P*M:=by
  let D:=fare (warehouse R) B 4
  let C:=1+8*D*(2:ℝ)^(e+1)
  have hd:0≤D:=sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _
  have cp:0<C:=by dsimp [C];positivity
  let coupon:=WilsonInvariantActionPrescribedReturn.original R simple (basis₀) J A Q τ (fun _=>0) Φ L E
    warm slow (q+2*(e+1)) h H (div_pos positive cp)
  filter_upwards [coupon] with m cards d clock o stages first period v P pp deposit
    r w M hp age later room shift y I γ a b predicted joint ν
  let z:=stock B (amounts R B (d.level+1) d.period (center R (d.level+1) d.cutoff d.period v))
  let initial:=fun i=>WilsonInvariantActionPrescribedReturn.reading R (basis₀) J Q τ (fun _=>0) d (fun _=>o)
    (pointTests (B:=B) R J) i
  let mask:=submitted R simple Q J A τ d o stages first period
  let term:=fun i V=>(initial i V-mask i V)*b V
  have enrolled(i:slots):Integrable (term i) ν ∧ (∫V,‖term i V‖ ∂ν)≤(ε/C)*γ^(q+2*(e+1))*M:=by
    have sold:=(cards d clock (fun _=>o) stages first period (WilsonOriginalPointModes.unit (target₀).tests)
      i).2 r w M hp age later room shift y I
    exact ⟨sold.1,sold.2.1⟩
  have receipt:=jordan ν (fun i=>normalization R (d.level+1)*z.2 i) term enrolled
  have eqp:joint=fun V=>∑i,(normalization R (d.level+1)*z.2 i)*term i V:=by
    funext V
    change (actualAverage R.family (N:=d.cutoff) a V-predicted V)*b V=_
    rw [WilsonInvariantActionCurvatureFrame.physical R Q J τ d simple (age.trans later) v o V]
    exact distribute _ (normalization R (d.level+1)) (b V) z.2 (fun i=>initial i V) (fun i=>mask i V)
      (fun i=>observable R Q τ d i o 1)
  rw [eqp]
  have price:=receipt.2.trans (payroll R Φ L U cut (d.level+1) d.cutoff d.period d.below v e q positive pp hp deposit)
  refine ⟨receipt.1,price,fun j past=>?_⟩
  exact (ActualWilsonAbsoluteTransport.first R.family R.makes d.below.le
    (WilsonRegisteredAxialEarlier.raw R.makes d.below.le receipt.1) past).trans price

end YM.Integration.WilsonInvariantActionCurvatureReturn
