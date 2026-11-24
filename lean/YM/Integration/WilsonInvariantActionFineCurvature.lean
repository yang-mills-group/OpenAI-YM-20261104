import YM.Integration.WilsonInvariantActionFineSource
import YM.Integration.WilsonInvariantActionCurvatureReturn
import YM.Integration.WilsonMatrixTicketLanesSelectedNormalization

noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonInvariantActionFineCurvature
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
open Extra.Trajectories MergeProof.Accent
open private posted from YM.Integration.WilsonInvariantActionCurvatureFrame
open private distribute from YM.Integration.WilsonInvariantActionCurvatureReturn
open scoped Classical Topology BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) {B:MS.Local.Physical.Deck G}
local notation "slots" => B.BIndex (4:ℤ) 2
local notation "u₀" => WilsonReportingPrescribedOldAction.label B
variable (J:Request (B.BIndex (4:ℤ) 2)) (A:NumericSchedule R.family J) (Q:MS.Land.Prescription B) (μ:ℝ)
variable (d:LocalFormal.Datum R.family (Stock.census (B.BIndex (4:ℤ) 2)))
variable (v:R.family.label 4) (o:Site (R.family.side (d.level+1) d.period))
local notation "live" => Nat.succ_le_of_lt d.below
local notation "J₀"=> ActualOriginalQPointSetup.request R (u₀) J
def unitTest : IndependentTests (ActualOriginalQPointSetup.request R (u₀) J).tests :=
  WilsonOriginalPointModes.unit _
local notation "X₀" => unitTest (B:=B) R J
local notation "points₀"=> fun _:slots=>o
local notation "orders₀"=> fun _:slots=>(0:ℕ)
local notation "D₀"=> ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) (points₀)
local notation "Ω"=> Config G (R.family.side (d.level+1) d.period)
local notation "stamp₀"=> WilsonMatrixTicketLanesSelectedNormalization.stamp (V:=slots) R μ d
local notation "τ₀"=> μ-R.family.S.scale (d.level+1)
local notation "g₀"=> regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "H₀"=> ActualOriginalQInitialInput.normalizer (V:=slots) R simple (u₀) J A d Q (points₀) (stamp₀) (orders₀)
local notation "X"=> WilsonInvariantActionFineSource.plain (V:=slots) R simple (u₀) J A d Q (points₀) (stamp₀) (orders₀) (X₀)
local notation "Y"=> WilsonInvariantActionFineSource.held (V:=slots) R simple (u₀) J A d Q (points₀) (stamp₀) (orders₀) (X₀)
local notation "A₀"=> R.family.O (d.level+1) d.period (WilsonMatrixTicketLanesReportedPivot.center R (d.level+1) d.cutoff d.period v) o
local notation "Γ₀"=> Stock.census slots
local notation "z₀"=> Prod.snd (WilsonMatrixOriginalCurvatureStock.stock B (WilsonMatrixOriginalIndependentFields.amounts R B
  (d.level+1) d.period (WilsonMatrixTicketLanesReportedPivot.center R (d.level+1) d.cutoff d.period v)))
local notation "s₀"=> WilsonMatrixOriginalCurvatureField.normalization R (d.level+1)

def masked (T:Ω):ℂ:=WilsonInvariantActionCurvatureFrame.assembled R Q (τ₀) d v o
  (fun i=>(H₀:ℂ)*((Y) T).part ((Γ₀).fire i))

def deficit (T:Ω):Marker.Poly (Γ₀):=(X) T-(Y) T

private theorem stamp_price:1≤H₀:=by
  have h:= (WilsonInvariantActionPrescribedReturn.normalization R simple (u₀) J A Q (τ₀) (orders₀) d (points₀)).1
  have eq:(τ₀)+R.family.S.scale d.cutoff=stamp₀:=by unfold WilsonMatrixTicketLanesSelectedNormalization.stamp; ring
  rw [eq] at h
  exact h

private theorem reading (i:slots) (T:Ω):
    WilsonInvariantActionCurvatureFrame.observable R Q (τ₀) d i o T=(H₀:ℂ)*((X) T).part ((Γ₀).fire i):=by
  let c:=fun _:slots=>(H₀:ℂ)⁻¹
  let t:=WilsonInvariantActionCurvatureFrame.pointTests (B:=B) R J
  have raw: (X) T=Mach (Γ₀) (fun l=>ActualRunQlocalNativeTuple.reader (D₀) l
      (VariableScaling.tests (D:=ActualRunQlocalNativeTuple.orbit (D₀)) c t l)*
      ActualOriginalCalibratedColumns.weightedObservable R B Q ((u₀) l)
        ((stamp₀)-R.family.S.scale d.cutoff) (R.family.side (d.level+1) d.period) o T 0):=by
    change (VariableScaling.packets c (ActualOriginalQFrozenInput.packets Q (D₀) (u₀)
      ((stamp₀)-R.family.S.scale d.cutoff) (orders₀) d.cutoff)).read t (g₀) T=_
    rw [VariableScaling.read]
    simpa only [ActualOriginalQPointSetup.pointDatum,ActualOriginalQPointDatum.root_eq] using
      ActualOriginalQFrozenInput.packets_read Q (D₀) (u₀) ((stamp₀)-R.family.S.scale d.cutoff) (orders₀)
        d.cutoff (live) (g₀) (VariableScaling.tests c t) T
  have unitPrice:ActualRunQlocalNativeTuple.reader (D₀) i (VariableScaling.tests
      (D:=ActualRunQlocalNativeTuple.orbit (D₀)) c t i)=(H₀:ℂ)⁻¹:=by
    have linear:ActualRunQlocalNativeTuple.reader (D₀) i
        (VariableScaling.tests (D:=ActualRunQlocalNativeTuple.orbit (D₀)) c t i)=
        c i*ActualRunQlocalNativeTuple.reader (D₀) i (t i):=by
      unfold VariableScaling.tests
      rw [map_smul]
      rfl
    rw [linear]
    rw [show ActualRunQlocalNativeTuple.reader (D₀) i (t i)=1 from
      (ActualOriginalQPointDatum.reader_eq R d.period (d.level+1) (fun _=>o) (fun j=>(J.tests j).D) (fun _=>0) i _).trans
      (WilsonOriginalPointModes.unit_read (J₀).tests i)]
    simp [c]
  have part (f:slots→ℂ):(Mach (Γ₀) f).part ((Γ₀).fire i)=f i:=by simp [Mach,Poly.part_sum,Poly.part_send]
  rw [raw,part,unitPrice,WilsonMatrixTicketLanesSelectedNormalization.clock,←mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le (stamp_price R simple J A Q μ d o)).ne'),one_mul]
  rfl

theorem difference (age:R.family.ref 4≤d.level+1) (T:Ω):
    (A₀) T-masked R simple J A Q μ d v o T =
      ∑i,((s₀)*(z₀) i)*(H₀:ℂ)*(deficit R simple J A Q μ d o T).part ((Γ₀).fire i):=by
  rw [posted R Q (τ₀) d simple age v o T]
  unfold masked WilsonInvariantActionCurvatureFrame.assembled
  simp only
  have eq:=distribute ((A₀) 1) (s₀) 1 (z₀)
    (fun i=>WilsonInvariantActionCurvatureFrame.observable R Q (τ₀) d i o T)
    (fun i=>(H₀:ℂ)*((Y) T).part ((Γ₀).fire i))
    (fun i=>WilsonInvariantActionCurvatureFrame.observable R Q (τ₀) d i o 1)
  simp only [mul_one] at eq
  rw [eq]
  apply sum_congr rfl
  intro i _
  rw [reading R simple J A Q μ d o i T]
  change _= _*(((X) T).part _-((Y) T).part _)
  ring

theorem gross (age:R.family.ref 4≤d.level+1) (T:Ω):
    ‖(A₀) T-masked R simple J A Q μ d v o T‖≤
      (∑i,‖(s₀)*(z₀) i‖)*(H₀)*Poly.price (fun _:slots=>1) (deficit R simple J A Q μ d o T):=by
  let D:=deficit R simple J A Q μ d o T
  have hh:0≤H₀:=zero_le_one.trans (stamp_price R simple J A Q μ d o)
  rw [difference R simple J A Q μ d v o age T]
  refine (norm_sum_le _ _).trans ?_
  rw [sum_mul,sum_mul]
  apply sum_le_sum
  intro i _
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hh]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) hh)
  simpa only [Poly.toll,prod_const_one,one_mul] using Poly.member
    (show ∀i:slots,0<(fun _:slots=>(1:ℝ)) i from fun _=>zero_lt_one) ((Γ₀).fire i) D

end YM.Integration.WilsonInvariantActionFineCurvature
