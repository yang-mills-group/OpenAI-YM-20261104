import YM.Integration.WilsonInvariantActionPrescribedReturn
import YM.Integration.WilsonMatrixOriginalCurvatureExperiments
import YM.Integration.WilsonMatrixOriginalGermEntryTariff
import YM.Integration.WilsonOriginalPointUnitTest
import YM.Integration.ActualWilsonConditionalRoots

/-! The true conditional mean of a submitted dimension-four primary in the original MS point basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionCurvatureFrame
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
open private issued_cont from YM.Integration.WilsonReportingPrescribedOldSignedPanel

variable {G:Gauge} {B:Deck G} (R:Run G) (Q:MS.Land.Prescription B)
local notation "slots" => B.BIndex (4:ℤ) 2
local notation "basis₀" => WilsonReportingPrescribedOldAction.label B
variable (J:Request (B.BIndex (4:ℤ) 2)) (τ:ℝ)
variable (d:LocalFormal.Datum R.family (Stock.census (B.BIndex (4:ℤ) 2)))
local notation "k" => d.level+1
local notation "nf" => R.family.side (k) d.period
local notation "target₀" => ActualOriginalQPointSetup.request R (basis₀) J
def pointTests : TestSpace (ActualOriginalQPointSetup.request R (basis₀) J).tests :=
  testInclusion (ActualOriginalQPointSetup.request R (basis₀) J).tests
    (WilsonOriginalPointModes.unit (ActualOriginalQPointSetup.request R (basis₀) J).tests)

def observable (i:slots) (o:Site (nf)) (T:Config G (nf)):ℂ:=
  ActualOriginalCalibratedColumns.weightedObservable R B Q ((basis₀) i) τ (nf) o T 0

def assembled (v:R.family.label 4) (o:Site (nf)) (y:slots→ℂ):ℂ:=
  let x:=center R (k) d.cutoff d.period v
  let z:=stock B (amounts R B (k) d.period x)
  R.family.O (k) d.period x o 1 + normalization R (k)*∑i,z.2 i*(y i-observable R Q τ d i o 1)

private theorem posted (simple:G.Simple) (age:R.family.ref 4≤(k))
    (v:R.family.label 4) (o:Site (nf)) (T:Config G (nf)):
    R.family.O (k) d.period (center R (k) d.cutoff d.period v) o T =
      assembled R Q τ d v o (fun i=>observable R Q τ d i o T):=by
  let x:=center R (k) d.cutoff d.period v
  let z:=stock B (amounts R B (k) d.period x)
  have posted:=WilsonMatrixOriginalCurvatureExperiments.observed R B (k) d.period Q simple age x τ o T 1
  change _-_=normalization R (k)*(operand R Q z τ 0 (nf) o T-operand R Q z τ 0 (nf) o 1) at posted
  unfold operand at posted
  change _=R.family.O (k) d.period x o 1+normalization R (k)*∑i,z.2 i*(observable R Q τ d i o T-observable R Q τ d i o 1)
  simp only [observable,mul_sub,sum_sub_distrib]
  apply eq_add_of_sub_eq'
  simpa only [if_pos rfl,add_sub_add_left_eq_sub,mul_sub] using posted

private theorem affine {Ω I:Type*} [MeasurableSpace Ω] (ν:Measure Ω) [IsProbabilityMeasure ν] [Fintype I]
    (c a:ℂ) (z b:I→ℂ) (f:I→Ω→ℂ) (hf:∀i,Integrable (f i) ν):
    (∫T,c+a*∑i,z i*(f i T-b i) ∂ν)=c+a*∑i,z i*((∫T,f i T ∂ν)-b i):=by
  have intg(i:I):Integrable (fun T=>z i*(f i T-b i)) ν:=((hf i).sub (integrable_const _)).const_mul _
  rw [integral_add (integrable_const _) ((integrable_finsetSum _ (fun i _=>intg i)).const_mul _),
    integral_const,probReal_univ,one_smul,integral_const_mul,integral_finsetSum _ (fun i _=>intg i)]
  simp only [integral_const_mul,integral_sub (hf _) (integrable_const _),integral_const,probReal_univ,one_smul]

theorem physical (simple:G.Simple) (age:R.family.ref 4≤(k))
    (v:R.family.label 4) (o:Site (nf)) (U:Config G (R.family.side d.level d.period)):
    actualAverage R.family (N:=d.cutoff) (R.family.O (k) d.period (center R (k) d.cutoff d.period v) o) U =
      assembled R Q τ d v o (fun i=>WilsonInvariantActionPrescribedReturn.reading R (basis₀) J Q τ
        (fun _=>0) d (fun _=>o) (pointTests (B:=B) R J) i U):=by
  let ν:=ActualWilsonConditionalRoots.fibre R.family (N:=d.cutoff) U
  letI:IsProbabilityMeasure ν:=ActualWilsonConditionalRoots.probability R.family R.makes d.below U
  let x:=center R (k) d.cutoff d.period v
  let z:=stock B (amounts R B (k) d.period x)
  have intg(i:slots):Integrable (observable R Q τ d i o) ν:=
    (issued_cont R Q ((basis₀) i) τ 0 o).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have one(i:slots):(ActualRunQlocalNativeTuple.reader (ActualOriginalQPointSetup.pointDatum R J d.period (k) (fun _=>o)) i)
      ((pointTests (B:=B) R J) i)=1:=
    (ActualOriginalQPointDatum.reader_eq R d.period (k) (fun _=>o) (fun j=>(J.tests j).D) (fun _=>0) i _).trans
      (WilsonOriginalPointModes.unit_read (target₀).tests i)
  have reading(i:slots):WilsonInvariantActionPrescribedReturn.reading R (basis₀) J Q τ (fun _=>0) d
      (fun _=>o) (pointTests (B:=B) R J) i U = ∫T,observable R Q τ d i o T ∂ν:=by
    rw [ActualWilsonConditionalRoots.average R.family R.makes d.below U]
    unfold WilsonInvariantActionPrescribedReturn.reading
    simp only [one,one_mul]
    rfl
  rw [←ActualWilsonConditionalRoots.average R.family R.makes d.below U]
  calc
    _=(∫T,assembled R Q τ d v o (fun i=>observable R Q τ d i o T) ∂ν):=
      integral_congr_ae (ae_of_all _ (posted R Q τ d simple age v o))
    _=R.family.O (k) d.period x o 1 + normalization R (k)*∑i,z.2 i*((∫T,observable R Q τ d i o T ∂ν)-observable R Q τ d i o 1):=
      affine ν (R.family.O (k) d.period x o 1) (normalization R (k)) z.2
        (fun i=>observable R Q τ d i o 1) (fun i=>observable R Q τ d i o) intg
    _=_:=by simp only [assembled,reading];rfl

end YM.Integration.WilsonInvariantActionCurvatureFrame

