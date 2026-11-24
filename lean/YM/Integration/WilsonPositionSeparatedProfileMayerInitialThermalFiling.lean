import YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalPin
import YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalSeries

/-! At fixed geometry, uniqueness of the Taylor expansion identifies every correctly regraded
coefficient of the physical compact Wilson coupon with the independently calculated forest row. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalFiling
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

theorem original (t:TestSpace (J₀).tests) (F:Forest (S).ratio) (tag:(S).Choices)
    (a:fieldDir G (R.family.side d.level d.period) 1) (s:(Stock.census V).Mode) (n:ℕ)
    (budget:BudgetPoint) (large:Bid.Larger (G:=G) (S))
    {P:Parcel.Oven (S).patch} (chart:P.Form G) (paid:P.Offers chart (S).kernel)
    (inside:∀z,‖Exterior.collect G a z‖≤chart.Q)
    (indextag:(Descent.nil (top:=R.family.side (d.level+1) d.period)).Tags):
    let l:=fun i:s.val=>u i.val
    let reader:=fun i:s.val=>WilsonPositionSeparatedProfileMayerInitialThermalWords.reader
      R hG u J A d Q o μ orders t i.val
    let site:=fun i:s.val=>ActualRunQlocalNativeTuple.root (D) i.val
    let cash:=WilsonMatrixTicketLanesTerminalQWords.coefficient R Q l (clock₀)
      (fun i:s.val=>orders i.val) reader
    let word:=WilsonMatrixTicketLanesTerminalQWords.word R l
    ∀k≤n,Laplace.detail (Order.ratio (Bulk.Fk (K) F tag (W t) a n)) s k=
      ∑z:∀i,WilsonMatrixTicketLanesTerminalQWords.Piece R (l i),
        WilsonPositionSeparatedProfileMayerInitialThermalSeries.deposited (cash z) (Spool.power (word z))
          (WilsonCoherentJointReturn.series (word z) (S) F R.metals.O (Exterior.collect G a) site large tag indextag) k:=by
  intro l reader site cash word k hk
  let A₀:=∀i,WilsonMatrixTicketLanesTerminalQWords.Piece R (l i)
  let row(z:A₀):=WilsonCoherentJointReturn.series (word z) (S) F R.metals.O (Exterior.collect G a)
    site large tag indextag
  let bareWord(z:A₀):=Spool.reads (word z) (S) (Exterior.collect G a) site
  have actual(z:A₀):PertExtension.Series.Tested.Aspiration (bareWord z) (row z):=
    WilsonPositionSeparatedProfileMayerInitialThermalSeries.word (word z) (S) F chart R.metals.O
      (Exterior.collect G a) site large tag indextag R.alloy.B.ratio paid inside
  have print:=WilsonPositionSeparatedProfileMayerInitialThermalSeries.finite cash
    (fun z:A₀=>Spool.power (word z)) bareWord row actual n
  have original:Laplace.Trial (Laplace.detail (Order.ratio (Bulk.Fk (K) F tag (W t) a n)) s)
      (fun h=>∑z:A₀,cash z*((h:ℂ)^Spool.power (word z)*bareWord z h)) n:=by
    apply Laplace.trial_congr _
      ((WilsonPositionSeparatedProfileMayerInitialThermalTrial.original R hG u J A d Q o μ orders
        profile hm hp t F tag a n budget).1 s)
    filter_upwards [PertExtension.Series.Tested.eventually_pos] with h hh
    simpa only [mul_assoc] using (WilsonPositionSeparatedProfileMayerInitialThermalPin.received
      R hG u J A d Q o μ orders profile hm hp t F tag a s hh)
  exact Laplace.trial_gap original print k hk

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalFiling
