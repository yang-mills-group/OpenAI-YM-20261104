import YM.Integration.WilsonInvariantActionOriginalQBirth
import YM.Integration.WilsonInvariantActionRegisteredReturn

/-! The independently charged and placed Q field can be submitted on the
genuine nonbare Wilson representation at any earlier date. Its measured
density and every transport retain the complete original vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionOriginalQCarry
open Function Filter Finset MeasureTheory Lattice RG Wilson Precision Marker Multi Exterior Tree
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric PhysicalNext.Repeat.Legato Comparison.RG02 Integral
open PhysicalNext.ThroughLaunch Source MergeProof.Accent IterationFour IterationFour.Vacuum WilsonLimitConstruction
open Actual Order Push.SectorMeasure Pert.Asymptotics OPE.Therm
open scoped Topology BigOperators Classical
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V] {B:MS.Local.Physical.Deck G}
  (R:Run G) (simple:G.Simple) (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
  (d:LocalFormal.Datum R.family (Stock.census V)) (Q:MS.Land.Prescription B)
  (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (orders:V→ℕ)
  (stages:WithStage R.metals.p OriginalRunConstruction.originalOrders)
  (first:ActualOriginalQInitialPreparation.start R simple u J A stages≤d.level)
  (period:(ActualOriginalQPointSetup.request R u J).physicalPeriodLower≤(R.family.S.period d.period).val)
local notation "H" => ActualOriginalQInitialPreparation.analyticInput R simple u J A d Q o μ orders stages first period
local notation "D" => ActualOriginalQInitialPreparation.input R simple u J A d Q o μ orders
local notation "JB" => ActualOriginalQPointSetup.request R u J
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "g" => regulatorRun R.family d.cutoff d.period (d.level+1)
open private references from YM.Integration.ActualOriginalQInitialPreparation

theorem density (t:TestSpace (JB).tests) (U:Config G (R.family.side (d.level+1) d.period)):
    ((D).leaf t).density U=ManuscriptQLocalActualLog.source R d (H) t U:=by
  rw [ManuscriptQLocalActualLog.literal]
  refine (ActualOriginalQInitialPreparation.input_density R simple u J A d Q o μ orders t U).trans ?_
  let centers:=ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
  let c:=ActualOriginalQInitialInput.scales R simple u J A d Q o μ orders
  let clock:=μ-R.family.S.scale d.cutoff
  change _=((P).eval U:ℂ) • Poly.pass ((VariableScaling.packets c
    (ActualOriginalQFrozenInput.packets Q centers u clock orders d.cutoff)).read t (g) U)
  rw [VariableScaling.read]
  exact ActualOriginalQFrozenInput.density_packet_factor Q centers u clock orders simple d.cutoff
    d.below (references R simple u J A d stages first) (g) (VariableScaling.tests c t) U

theorem history (t:TestSpace (JB).tests) {j:ℕ} (cut:j≤d.level+1) (U:Config G (R.family.side j d.period)):
    (R.family.path.rep d.cutoff d.period j).eval U • actualTransport R.family (N:=d.cutoff)
      (fun X=>Poly.pass ((H).packets.read t (g) X)) cut U=
      gust R.family.path d.cutoff d.period (d.level+1) ((D).leaf t).density j cut U:=by
  rw [actualTransport_unnormalize R.family R.makes (Nat.succ_le_of_lt d.below)]
  congr 1;funext X
  exact (Complex.coe_smul ((P).eval X) _).symm.trans
    ((density R simple u J A d Q o μ orders stages first period t X).trans
      (ManuscriptQLocalActualLog.literal R d (H) t X)).symm

end YM.Integration.WilsonInvariantActionOriginalQCarry
