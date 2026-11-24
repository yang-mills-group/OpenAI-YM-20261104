import YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalTrial
import YM.Integration.WilsonMatrixTicketLanesTerminalQWords

/-! The authentic scaled Q test gives the same finite physical Wilson words at every positive
temperature in the fixed-cutoff Taylor calibration. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalWords
open Function Filter Lattice Wilson RG Precision Tree Marker Multi Exterior
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global MergeProof.Accent
open FullQLocal FullQLocal.RenderedStep IterationFour IterationFour.Vacuum
open Comparison.RG02 Comparison.RG02.Order Pert.Asymptotics WilsonLimitConstruction
open scoped Classical Topology BigOperators

variable {G:Gauge} {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V]
  (R:Run G) (hG:G.Simple) (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
  (d:LocalFormal.Datum R.family (Stock.census V)) (Q:MS.Land.Prescription B)
  (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (orders:V→ℕ)
local notation "D" => ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "c₀" => ActualOriginalQInitialInput.scales R hG u J A d Q o μ orders
local notation "P" => ActualOriginalQInitialInput.packets R hG u J A d Q o μ orders
local notation "clock₀" => μ-R.family.S.scale d.cutoff

def reader (t:TestSpace (J₀).tests) (i:V):ℂ:=
  ActualRunQlocalNativeTuple.reader (D) i (VariableScaling.tests (c₀) t i)

theorem marks (t:TestSpace (J₀).tests) (h:ℝ) (U:Config G (R.family.side (d.level+1) d.period)):
    (P).read t h U=Mach (Stock.census V) (fun i=>reader R hG u J A d Q o μ orders t i *
      ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) (clock₀)
        _ (ActualRunQlocalNativeTuple.root (D) i) U (orders i)):=by
  unfold ActualOriginalQInitialInput.packets
  rw [VariableScaling.read]
  exact ActualOriginalQFrozenInput.packets_read Q (D) u (clock₀) orders d.cutoff d.below h _ U

theorem mode (t:TestSpace (J₀).tests) (h:ℝ) (U:Config G (R.family.side (d.level+1) d.period))
    (s:(Stock.census V).Mode):
    (Poly.pass ((P).read t h U)).part s=
      WilsonMatrixTicketLanesTerminalQWords.marked R Q (fun i:s.val=>u i.val) (clock₀)
        (fun i:s.val=>orders i.val) (fun i:s.val=>reader R hG u J A d Q o μ orders t i.val)
        (fun i:s.val=>ActualRunQlocalNativeTuple.root (D) i.val) U:=by
  rw [marks R hG u J A d Q o μ orders t h U,Mach,Extra.Trajectories.pass_fire]
  exact (Finset.prod_attach s.val _).symm

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalWords
