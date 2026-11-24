import YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalMeasure
import YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalWords

/-! The exact all-temperature normalized observed Wilson word of each original Q mode. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalPin
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

theorem sample {n:Side} (a:fieldDir G n 1) (h:ℝ):
    Integral.sample h a=Parcel.Oven.slice (collect G a) h:=by
  funext e
  simp [Integral.sample,represent,RG.increment,Exterior.collect,Parcel.Oven.slice]

theorem received (t:TestSpace (J₀).tests) (F:Forest (S).ratio) (tag:(S).Choices)
    (a:fieldDir G (R.family.side d.level d.period) 1) (s:(Stock.census V).Mode) {h:ℝ} (positive:0<h):
    let l:=fun i:s.val=>u i.val
    let ks:=fun i:s.val=>orders i.val
    let reader:=fun i:s.val=>WilsonPositionSeparatedProfileMayerInitialThermalWords.reader
      R hG u J A d Q o μ orders t i.val
    let site:=fun i:s.val=>ActualRunQlocalNativeTuple.root (D) i.val
    (Order.unitScale (Bare.realMoment (K) F (W t) tag a h)).part s=
      ∑z:∀i,WilsonMatrixTicketLanesTerminalQWords.Piece R (l i),
        WilsonMatrixTicketLanesTerminalQWords.coefficient R Q l (clock₀) ks reader z*
        (h:ℂ)^Spool.power (WilsonMatrixTicketLanesTerminalQWords.word R l z)*
        Spool.reads (WilsonMatrixTicketLanesTerminalQWords.word R l z) (S) (collect G a) site h:=by
  intro l ks reader site
  rw [WilsonPositionSeparatedProfileMayerInitialThermalMeasure.physical R hG u J A d Q o μ orders
    profile hm hp t F tag a s positive,sample]
  have times:Integral.temperature h=h⁻¹^2:=by simp [Integral.temperature]
  simp_rw [times,WilsonPositionSeparatedProfileMayerInitialThermalWords.mode R hG u J A d Q o μ orders t h]
  refine (WilsonMatrixTicketLanesTerminalQWords.pinned R Q l (clock₀) ks reader (S) (collect G a) site h positive
    (R.family.path.levels.transition_mass d.level d.period _)).trans ?_
  exact Finset.sum_congr (Finset.ext fun _=>by simp) (fun _ _=>rfl)

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalPin
