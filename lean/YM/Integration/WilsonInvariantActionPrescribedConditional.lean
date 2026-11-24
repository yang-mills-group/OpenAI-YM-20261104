import YM.Integration.WilsonInvariantActionReportedQMoment
import YM.Integration.WilsonInvariantActionMeasuredQReturn
import YM.Extra.MULTISOURCE_TRAJECTORIES.Initial

/-! The single original marked observable in the genuine previously prescribed
program, on the normalized interacting Wilson transition. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionPrescribedConditional
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

variable {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V}

private theorem single (p:Poly Γ) (hp:p.part Γ.quiet=1) (i:V):
    (Extra.Trajectories.connected p).part (Γ.fire i)=p.part (Γ.fire i):=by
  classical
  have distinct:Γ.fire i≠Γ.quiet:=by
    intro h
    have h':({i}:Finset V)=∅:=congrArg Subtype.val h
    simp at h'
  have zero:(p-1).part Γ.quiet=0:=by simp [sub_eq_add_neg,hp]
  have existsV:0<Fintype.card V:=Fintype.card_pos_iff.mpr ⟨i⟩
  rw [RG02.Marks.connected_eq_logTable hp,RG02.Marks.logTable,Poly.part_sum]
  rw [Finset.sum_eq_single 0]
  · simp [sub_eq_add_neg,distinct]
  · intro k _ hk
    have small:(Γ.fire i).val.card<k+1:=by
      change ({i}:Finset V).card<k+1
      rw [Finset.card_singleton]
      omega
    rw [Poly.part_smul,Poly.high _ zero _ _ small,mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr existsV))

variable {G:Gauge} {B:MS.Local.Physical.Deck G} (R:Run G) (simple:G.Simple)
  (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
  (d:LocalFormal.Datum R.family (Stock.census V)) (Q:MS.Land.Prescription B)
  (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (orders:V→ℕ)
  (stages:WithStage R.metals.p OriginalRunConstruction.originalOrders)
  (first:ActualOriginalQInitialPreparation.start R simple u J A stages≤d.level)
  (period:(ActualOriginalQPointSetup.request R u J).physicalPeriodLower≤(R.family.S.period d.period).val)
local notation "F₀" => ActualOriginalQInitialPreparation.analyticInput R simple u J A d Q o μ orders stages first period
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "D₀" => ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
local notation "c₀" => ActualOriginalQInitialInput.scales R simple u J A d Q o μ orders
local notation "g" => regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "fine" => Config G (R.family.side (d.level+1) d.period)
local notation "coarse" => Config G (R.family.side d.level d.period)

include stages first period in
theorem source (t:TestSpace (J₀).tests) (γ:ℝ) (T:fine):
    (F₀).packets.read t γ T=Mach (Stock.census V) (fun i=>
      ActualRunQlocalNativeTuple.reader (D₀) i (VariableScaling.tests (D:=ActualRunQlocalNativeTuple.orbit (D₀)) (c₀) t i)*
        ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) (μ-R.family.S.scale d.cutoff)
           (R.family.side (d.level+1) d.period) (o i) T (orders i)):=by
  change (VariableScaling.packets (c₀) (ActualOriginalQFrozenInput.packets Q (D₀) u
    (μ-R.family.S.scale d.cutoff) orders d.cutoff)).read t γ T=_
  rw [VariableScaling.read]
  simpa only [ActualOriginalQPointSetup.pointDatum,ActualOriginalQPointDatum.root_eq] using
    ActualOriginalQFrozenInput.packets_read Q (D₀) u (μ-R.family.S.scale d.cutoff) orders d.cutoff
      (Nat.succ_le_of_lt d.below) γ (VariableScaling.tests (c₀) t) T

include stages first period in
theorem conditional (x:IndependentTests (J₀).tests) (i:V) (U:coarse):
    let t:=testInclusion (J₀).tests x
    let X:=(F₀).packets.read t (g)
    (ManuscriptQLocalMeasuredMarkTransport.logarithm R.family (N:=d.cutoff) X U).part ((Stock.census V).fire i)=
      actualAverage R.family (N:=d.cutoff) (fun T=>ActualRunQlocalNativeTuple.reader (D₀) i (VariableScaling.tests (D:=ActualRunQlocalNativeTuple.orbit (D₀)) (c₀) t i)*
        ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) (μ-R.family.S.scale d.cutoff)
          (R.family.side (d.level+1) d.period) (o i) T (orders i)) U:=by
  intro t X
  let P:=(R.family.path.rep d.cutoff d.period (d.level+1)).p
  have hz T:=(ManuscriptQLocalOriginalFineMaskLoss.means_quiet (F₀).packets (F₀).input_paid x P T).1
  unfold ManuscriptQLocalMeasuredMarkTransport.logarithm ManuscriptQLocalMeasuredMarkTransport.bank
  rw [single _ (moment_quiet R.family R.makes d.below U (fun _=>X) 1 hz),moment_part]
  congr 1
  funext T
  change (Poly.pass ((F₀).packets.read t (g) T)).part _=_
  rw [source R simple u J A d Q o μ orders stages first period]
  unfold Mach
  rw [Extra.Trajectories.pass_fire]
  simp only [Census.fire,Finset.prod_singleton]

end YM.Integration.WilsonInvariantActionPrescribedConditional
