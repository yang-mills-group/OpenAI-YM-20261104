import YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalRoster
import YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalSum
import YM.Integration.WilsonMatrixTicketLanesTerminalQGrades

/-! The paid absolute finite sum evaluates exactly the independently assigned normalized
Wilson Taylor coefficient on its original surveyor’s actual physical pin. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalDisplay
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

theorem measured {r:ℕ} (t:TestSpace (J₀).tests) (F:Forest (S).ratio) (tag:(S).Choices)
    (a:fieldDir G (R.family.side d.level d.period) 1) (s:(Stock.census V).Mode) (e:Fin r≃s.val):
    let l:=fun i:Fin r=>u (e i).val
    let reader:=fun i:Fin r=>WilsonPositionSeparatedProfileMayerInitialThermalWords.reader
      R hG u J A d Q o μ orders t (e i).val
    let site:=fun i:Fin r=>ActualRunQlocalNativeTuple.root (D) (e i).val
    (Order.unitScale (Bare.realMoment (K) F (W t) tag a (g₀))).part s=
      WilsonMatrixTicketLanesTerminalQReturn.measured R Q l (clock₀) (fun i=>orders (e i).val)
        reader (Exterior.collect G a) site:=by
  intro l reader site
  rw [WilsonPositionSeparatedProfileMayerInitialThermalMeasure.physical R hG u J A d Q o μ orders
    profile hm hp t F tag a s ((WilsonCoherentInheritedSpool.temperature R hG d.level (d.level+1) d.period le_rfl).2.1),WilsonPositionSeparatedProfileMayerInitialThermalPin.sample]
  have times:Integral.temperature (g₀)=(g₀)⁻¹^2:=by simp [Integral.temperature]
  simp_rw [times,WilsonPositionSeparatedProfileMayerInitialThermalRoster.mode R hG u J A d Q o μ orders t (g₀) _ s e]
  rfl

theorem filed {r:ℕ} (t:TestSpace (J₀).tests) (F:Forest (S).ratio) (tag:(S).Choices)
    (a:fieldDir G (R.family.side d.level d.period) 1) (s:(Stock.census V).Mode) (e:Fin r≃s.val)
    (n:ℕ) (budget:BudgetPoint) (large:Bid.Larger (G:=G) (S))
    (cap:ℝ) (positive:0<cap) (inside:∀i,‖Exterior.collect G a i‖≤cap)
    (indextag:(Descent.nil (top:=R.family.side (d.level+1) d.period)).Tags)
    (degree:∀z:∀i,WilsonMatrixTicketLanesTerminalQWords.Piece R (u (e i).val),
       Spool.power (WilsonMatrixTicketLanesTerminalQWords.word R (fun i=>u (e i).val) z)≤n):
    let l:=fun i:Fin r=>u (e i).val
    let reader:=fun i:Fin r=>WilsonPositionSeparatedProfileMayerInitialThermalWords.reader
      R hG u J A d Q o μ orders t (e i).val
    let site:=fun i:Fin r=>ActualRunQlocalNativeTuple.root (D) (e i).val
    (Order.value ((g₀):ℂ) (Order.ratio (Bulk.Fk (K) F tag (W t) a n))).part s=
      WilsonMatrixTicketLanesTerminalQGrades.stack R Q l n (clock₀) (fun i=>orders (e i).val) reader
        large F (Exterior.collect G a) site tag indextag:=by
  intro l reader site
  let word:=WilsonMatrixTicketLanesTerminalQWords.word R l
  let cash:=WilsonMatrixTicketLanesTerminalQWords.coefficient R Q l (clock₀) (fun i:Fin r=>orders (e i).val) reader
  let A₀:=∀i,WilsonMatrixTicketLanesTerminalQWords.Piece R (l i)
  let row(z:A₀):=WilsonCoherentJointReturn.series (word z) (S) F R.metals.O (Exterior.collect G a)
    site large tag indextag
  let coeff(k:ℕ):=∑z:A₀,WilsonPositionSeparatedProfileMayerInitialThermalSeries.deposited (cash z)
    (Spool.power (word z)) (row z) k
  obtain ⟨P,chart,width,cost,_⟩:=WilsonCoherentFiniteIssue.purchased R d.level (K).branches cap positive
  have identity:=WilsonPositionSeparatedProfileMayerInitialThermalRoster.filed R hG u J A d Q o μ orders
    profile hm hp t F tag a s e n budget large chart cost (fun i=>(inside i).trans_eq width.symm) indextag
  rw [←Laplace.tests]
  calc
    _ = PertExtension.Series.Tested.peval coeff n (g₀):=by
      unfold PertExtension.Series.Tested.peval PertExtension.Series.Zone.eval
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      refine (identity k (Finset.mem_range_succ_iff.mp hk)).trans ?_
      exact Finset.sum_congr (Finset.ext fun _=>by simp) (fun _ _=>rfl)
    _ = _:=by
      refine (WilsonPositionSeparatedProfileMayerInitialThermalSum.total cash
        (fun z:A₀=>Spool.power (word z)) row degree (g₀)).trans ?_
      exact Finset.sum_congr (Finset.ext fun _=>by simp) (fun _ _=>rfl)

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalDisplay
