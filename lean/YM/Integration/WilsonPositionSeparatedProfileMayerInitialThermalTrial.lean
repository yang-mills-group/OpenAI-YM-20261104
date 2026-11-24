import YM.Integration.WilsonLimitConstruction.FundedMatchedPointOpening
import YM.Comparison.RG02.Bare.View

/-! On a fixed physical regulator the independently filed initial Wilson colours have the actual
variable-temperature normalized Haar expansion, including every connected marked coefficient. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalTrial
open Function Filter Lattice Wilson RG Precision Tree Marker Multi Exterior
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global NativePaidPacketGroups
open FullQLocal FullQLocal.RenderedStep IterationFour IterationFour.Vacuum
open Comparison.RG02 Comparison.RG02.Order Pert.Asymptotics WilsonLimitConstruction
open scoped Classical Topology BigOperators

private theorem frozen {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] {n:Side}
    {Γ:Census V} {E:V→YM.ComparisonDensity.Address.Orbit} (P:MarkedPackets E G n Γ)
    (g:ℝ) (v:ℝ → Config G n→ℝ) (t:TestSpace E):
    let W:=NativePaidPacketColors.colors (ActualPacketCouplingFreeze.freeze P g) v t
    ∀i h,0<h → ∀U,W.mark i h U=(h^W.power i) • W.mark i 1 U:=by
  intro W i h _ U
  dsimp only [W,NativePaidPacketColors.colors]
  rw [one_pow,one_smul,ActualPacketCouplingFreeze.freeze_read,ActualPacketCouplingFreeze.freeze_read]

variable {G:Gauge} {D:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V]
  (R:Run G) (hG:G.Simple) (u:V→MS.Rake.Label D) (J:Request V) (A:NumericSchedule R.family J)
  (d:LocalFormal.Datum R.family (Stock.census V)) (Q:MS.Land.Prescription D)
  (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (orders:V→ℕ)
  (profile:∀k,k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power)
  (hm:ActualOriginalQInitialInput.start R hG u J A profile≤d.level)
  (hp:(ActualOriginalQPointSetup.request R u J).physicalPeriodLower≤(R.family.S.period d.period).val)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "P" => ActualOriginalQInitialInput.input R hG u J A d Q o μ orders profile hm hp
local notation "W" => FundedMatchedPointOpening.colors R hG u J A d Q o μ orders profile hm hp
local notation "K" => (RunFormalChain.fromRun R).step (d.level+1) d.level d.period (Nat.lt_succ_self _)
local notation "S" => R.family.path.levels.clock.op d.level d.period

theorem witnessed (t:TestSpace (J₀).tests):Bare.Witnessed (W t) (K):=by
  apply NativeWilsonColoredMeasure.frozen_witnessed R d.level d.period ((P).colors t) ((P).convention.well t)
  exact frozen _ _ (fun _ _=>0) _

theorem original (t:TestSpace (J₀).tests) (F:Forest (S).ratio) (tag:(S).Choices)
    (a:fieldDir G (R.family.side d.level d.period) 1) (n:ℕ) (budget:BudgetPoint):
    Laplace.Fleet.Test (Order.ratio (Bulk.Fk (K) F tag (W t) a n))
        (fun h=>Order.unitScale (Bare.realMoment (K) F (W t) tag a h)) ∧
    Laplace.Fleet.Test (Order.logMarked (Bulk.Fk (K) F tag (W t) a n))
        (fun h=>Extra.Trajectories.connected (Order.unitScale (Bare.realMoment (K) F (W t) tag a h))):=by
  exact (Bare.wilson_step_test (K) F (W t) tag a n budget
    (witnessed R hG u J A d Q o μ orders profile hm hp t)).2.2

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalTrial
