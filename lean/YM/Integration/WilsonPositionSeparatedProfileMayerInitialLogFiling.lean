import YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalDisplay
import YM.Integration.WilsonMatrixTicketLanesTerminalQSeries

/-! Each absolute thermal coefficient on the same finite Wilson forest and spatial reporting sources. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogFiling
open Function Filter Lattice Wilson RG Precision Tree Marker Multi Exterior
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep IterationFour IterationFour.Vacuum
open Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Actual Pert.Asymptotics WilsonLimitConstruction
open scoped Classical Topology BigOperators

variable {G:Gauge} {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V]
  (R:Run G) (hG:G.Simple) (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
  (d:LocalFormal.Datum R.family (Stock.census V)) (Q:MS.Land.Prescription B)
  (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (orders:V→ℕ)
  (profile:∀k,k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power)
  (hm:ActualOriginalQInitialInput.start R hG u J A profile≤d.level)
  (hp:(ActualOriginalQPointSetup.request R u J).physicalPeriodLower≤(R.family.S.period d.period).val)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "W" => FundedMatchedPointOpening.colors R hG u J A d Q o μ orders profile hm hp
local notation "K" => (RunFormalChain.fromRun R).step (d.level+1) d.level d.period (Nat.lt_succ_self _)
local notation "S" => R.family.path.levels.clock.op d.level d.period

local notation "D" => ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
local notation "clock₀" => μ-R.family.S.scale d.cutoff
open FVA2.CityHistory RGComparison.Core16

open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice

local notation "g₀" => regulatorRun R.family (d.level+1) d.period (d.level+1)

theorem coefficient {r:ℕ} (t:TestSpace (J₀).tests) (F:Forest (S).ratio) (tag:(S).Choices)
    (a:fieldDir G (R.family.side d.level d.period) 1) (s:(Stock.census V).Mode) (e:Fin r≃s.val)
    (n:ℕ) (budget:BudgetPoint) (large:Bid.Larger (G:=G) (S))
    (cap:ℝ) (positive:0<cap) (inside:∀i,‖Exterior.collect G a i‖≤cap)
    (indextag:(Descent.nil (top:=R.family.side (d.level+1) d.period)).Tags):
    let l:=fun i:Fin r=>u (e i).val
    let reader:=fun i:Fin r=>WilsonPositionSeparatedProfileMayerInitialThermalWords.reader
      R hG u J A d Q o μ orders t (e i).val
    let site:=fun i:Fin r=>ActualRunQlocalNativeTuple.root (D) (e i).val
    ∀j≤n,Laplace.detail (Order.ratio (Bulk.Fk (K) F tag (W t) a n)) s j=
      WilsonMatrixTicketLanesTerminalQSeries.term R Q l (clock₀) (fun i=>orders (e i).val) reader j
        large F (Exterior.collect G a) site tag indextag:=by
  intro l reader site
  obtain ⟨P,chart,width,cost,_⟩:=WilsonCoherentFiniteIssue.purchased R d.level (K).branches cap positive
  have sequence:=WilsonPositionSeparatedProfileMayerInitialThermalRoster.filed R hG u J A d Q o μ orders
    profile hm hp t F tag a s e n budget large chart cost (fun i=>(inside i).trans_eq width.symm) indextag
  intro j hj
  refine (sequence j hj).trans ?_
  unfold WilsonMatrixTicketLanesTerminalQSeries.term
  apply Finset.sum_congr (Finset.ext fun _=>by simp)
  intro z _
  rw [WilsonPositionSeparatedProfileMayerInitialThermalSum.coefficient]
  simp only [mul_ite,mul_zero]
  rfl

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogFiling
