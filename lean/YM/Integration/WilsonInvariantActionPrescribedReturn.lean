import YM.Integration.WilsonInvariantActionPrescribedConditional
import YM.Integration.WilsonReportingPrescribedOldScale

/-! Undo the actual original marked test normalization at a fixed independent
reference clock and measure its single occurrence against older grade-four fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionPrescribedReturn
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
open private capped from YM.Integration.WilsonReportingPrescribedOldScale
variable {V:Type} [DecidableEq V] [Fintype V] {G:Gauge} {B:MS.Local.Physical.Deck G}
  (R:Run G) (simple:G.Simple) (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
  (Q:MS.Land.Prescription B) (τ:ℝ) (orders:V→ℕ)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "A₀" => ActualOriginalQInitialInput.schedule R simple u J A
local notation "base" => ActualOriginalQPointSetup.pointDatum R J 0 0 (fun _=>0)

def ceiling := (1+∑s:Slot u,‖fee Q u τ orders s‖)*max 1 (totalRowPrice (base) u (fun _=>1) 1)

variable (d:LocalFormal.Datum R.family (Stock.census V)) (o:V→Site (R.family.side (d.level+1) d.period))
local notation "µ₀" => τ+R.family.S.scale d.cutoff
local notation "H₀" => ActualOriginalQInitialInput.normalizer R simple u J A d Q o (µ₀) orders
local notation "D₀" => ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
local notation "c₀" => ActualOriginalQInitialInput.scales R simple u J A d Q o (µ₀) orders
local notation "g" => regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "fine" => Config G (R.family.side (d.level+1) d.period)
local notation "coarse" => Config G (R.family.side d.level d.period)

include o in
theorem normalization : 1≤H₀ ∧ H₀≤ceiling R u J Q τ orders:=by
  refine ⟨le_max_left _ _,capped R simple u J A d Q o (µ₀) orders ?_ ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _=>norm_nonneg _)
  intro s
  rw [add_sub_cancel_right]
  exact (Finset.single_le_sum (fun j (_:j∈(Finset.univ:Finset (Slot u)))=>norm_nonneg (fee Q u τ orders j))
    (Finset.mem_univ s)).trans (le_add_of_nonneg_left zero_le_one)

def reading (t:TestSpace (J₀).tests) (i:V) (U:coarse):ℂ:=
  actualAverage R.family (N:=d.cutoff) (fun T=>ActualRunQlocalNativeTuple.reader (D₀) i (t i)*
    ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) τ
        (R.family.side (d.level+1) d.period) (o i) T (orders i)) U

variable (stages:WithStage R.metals.p OriginalRunConstruction.originalOrders)
  (first:ActualOriginalQInitialPreparation.start R simple u J A stages≤d.level)
  (period:(ActualOriginalQPointSetup.request R u J).physicalPeriodLower≤(R.family.S.period d.period).val)
local notation "F₀" => ActualOriginalQInitialPreparation.analyticInput R simple u J A d Q o (µ₀) orders stages first period

include first period in
theorem restored (x:IndependentTests (J₀).tests) (i:V) (U:coarse):
    let t:=testInclusion (J₀).tests x
    let X:=(F₀).packets.read t (g)
    reading R u J Q τ orders d o t i U=(H₀:ℂ)*
      (ManuscriptQLocalMeasuredMarkTransport.logarithm R.family (N:=d.cutoff) X U).part ((Stock.census V).fire i):=by
  intro t X
  rw [WilsonInvariantActionPrescribedConditional.conditional R simple u J A d Q o (µ₀) orders stages first period x i U]
  have positive:0<H₀:=zero_lt_one.trans_le (normalization R simple u J A Q τ orders d o).1
  have hn:(H₀:ℂ)≠0:=Complex.ofReal_ne_zero.mpr positive.ne'
  have linear:(ActualRunQlocalNativeTuple.reader (D₀) i)
      (VariableScaling.tests (D:=ActualRunQlocalNativeTuple.orbit (D₀)) (c₀) t i)=
      (H₀:ℂ)⁻¹*(ActualRunQlocalNativeTuple.reader (D₀) i) (t i):=by
    unfold VariableScaling.tests
    rw [map_smul]
    rfl
  unfold reading actualAverage
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with T
  dsimp only [t] at linear ⊢
  simp only [Complex.real_smul,linear,add_sub_cancel_right]
  field_simp [hn]

variable {f:Extraction.Order} {S:Table R.family.book} (Φ:Spec.Final R.family f S) (L:RG17.Layout Φ)
  (E:OPE.Services R.family f S)

set_option backward.isDefEq.respectTransparency false in
include E in
theorem original (warm:Poetry R.family.path.levels)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (q h H:ℕ) {ε:ℝ} (positive:0<ε):
    ∀ᶠm:ℕ in atTop,∀(d:LocalFormal.Datum R.family (Stock.census V)),d.level=m→
    ∀(o:V→Site (R.family.side (d.level+1) d.period))
      (stages:WithStage R.metals.p OriginalRunConstruction.originalOrders)
      (first:ActualOriginalQInitialPreparation.start R simple u J A stages≤d.level)
      (period:(ActualOriginalQPointSetup.request R u J).physicalPeriodLower≤(R.family.S.period d.period).val)
      (x:IndependentTests (J₀).tests) (i:V),
      let inputClock:=τ+R.family.S.scale d.cutoff
      let F:=ActualOriginalQInitialPreparation.analyticInput R simple u J A d Q o inputClock orders stages first period
      let normalizer:=ActualOriginalQInitialInput.normalizer R simple u J A d Q o inputClock orders
      let T:=testInclusion (J₀).tests x
      let measuredG:=regulatorRun R.family d.cutoff d.period (d.level+1)
      let P:=(R.family.path.rep d.cutoff d.period (d.level+1)).p
      let Y:=ManuscriptQLocalOriginalConditionalTail.source F.packets P measuredG x 1
      let change:=fun U=>reading R u J Q τ orders d o T i U-(normalizer:ℂ)*
        (ManuscriptQLocalMeasuredMarkTransport.logarithm R.family (N:=d.cutoff) Y U).part ((Stock.census V).fire i)
      let ν:=scene R.family.path d.cutoff d.period d.level
      Integrable change ν ∧
        ∀(r:ℝ) (w₀:R.family.label 4) (M:ℝ),0≤M → R.family.ref 4≤L.level r → L.level r≤d.level+1 →
          R.family.S.a (L.level r)/R.family.S.a (d.level+1)≤R.family.path.levels.clock.hatBeta (d.level+1)^H →
          mass R.family 4 (L.shift 4 r w₀)≤R.family.path.levels.clock.hatBeta (L.level r)^h*M →
          ∀(y:Site (R.family.side (d.level+1) d.period)) (I:Set ℕ),
            let b:=centered R (Nat.le_succ _) d.below (RG17.atRef L 4 r (d.cutoff,d.period) w₀) y I
            let joint:=fun U=>change U*b U
            Integrable joint ν ∧ (∫U,‖joint U‖ ∂ν)≤ε*measuredG^q*M ∧
              ∀(j:ℕ) (past:j≤d.level),(∫W,‖actualTransport R.family (N:=d.cutoff) joint past W‖
                ∂scene R.family.path d.cutoff d.period j)≤ε*measuredG^q*M:=by
  let C:=ceiling R u J Q τ orders
  have cp:0<C:=mul_pos (add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun _ _=>norm_nonneg _))
    (zero_lt_one.trans_le (le_max_left _ _))
  have bought:=WilsonInvariantActionMeasuredQReturn.original (Γ:=Stock.census V) R (J₀) (A₀) Φ L E simple warm slow q h H
    (div_pos positive cp)
  filter_upwards [bought] with m bought
  intro d eq
  subst m
  intro o stages first period x i ck F normalizer T measuredG P Y change ν
  let X:=F.packets.read T measuredG
  let raw:=fun U=>(ManuscriptQLocalMeasuredMarkTransport.logarithm R.family (N:=d.cutoff) X U).part ((Stock.census V).fire i)-
    (ManuscriptQLocalMeasuredMarkTransport.logarithm R.family (N:=d.cutoff) Y U).part ((Stock.census V).fire i)
  have tally:=bought d rfl F x ((Stock.census V).fire i)
  have tm:Poly.toll (fun j=>F.inputRadii j / F.kernelCosts j) ((Stock.census V).fire i)=1:=by
    change Poly.toll (fun _:V=>(1:ℝ)/1) ((Stock.census V).fire i)=1
    simp [Poly.toll]
  simp only [tm,Complex.ofReal_one,one_mul] at tally
  have factor:change=fun U=>(normalizer:ℂ)*raw U:=by
    funext U
    unfold change raw
    rw [restored R simple u J A Q τ orders d o stages first period x i U,mul_sub]
  have charge:=normalization R simple u J A Q τ orders d o
  have nH:‖(normalizer:ℂ)‖=normalizer:=by rw [Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans charge.1)]
  refine ⟨by rw [factor];exact tally.1.const_mul _,?_⟩
  intro r w₀ M hM age later room shift y I b joint
  let paired:=fun U=>raw U*b U
  obtain ⟨intg,rawpaid,-⟩:=tally.2.2 r w₀ M hM age later room shift y I
  change Integrable paired ν at intg
  change (∫U,‖paired U‖ ∂ν)≤(ε/C)*measuredG^q*M at rawpaid
  have eqp:joint=fun U=>(normalizer:ℂ)*paired U:=by funext U;change change U*b U=_;rw [factor];exact mul_assoc .. 
  have income:Integrable joint ν:=by rw [eqp];exact intg.const_mul _
  have price:(∫U,‖joint U‖ ∂ν)≤ε*measuredG^q*M:=calc
    _=normalizer*(∫U,‖paired U‖ ∂ν):=by simp only [eqp,norm_mul,nH,integral_const_mul]
    _≤C*((ε/C)*measuredG^q*M):=mul_le_mul charge.2 rawpaid (integral_nonneg fun _=>norm_nonneg _) cp.le
    _=ε*measuredG^q*M:=by field_simp
  refine ⟨income,price,fun j past=>?_⟩
  exact (ActualWilsonAbsoluteTransport.first R.family R.makes d.below.le
    (WilsonRegisteredAxialEarlier.raw R.makes d.below.le income) past).trans price

end YM.Integration.WilsonInvariantActionPrescribedReturn
