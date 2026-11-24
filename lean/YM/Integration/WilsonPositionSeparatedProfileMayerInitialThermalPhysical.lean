import YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalTrial
import YM.Integration.PhysicalWilsonBornMaterial
import YM.Comparison.RG02.Order.Pay

/-! The first measured Wilson response of the genuinely deposited full original Q input, at
its own cutoff, is the same normalized finite moment used in its thermal expansion. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalPhysical
open Function Filter Lattice Wilson RG Precision Tree Marker Multi Exterior
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global NativePaidPacketGroups
open FullQLocal FullQLocal.RenderedStep IterationFour IterationFour.Vacuum
open Comparison.RG02 Comparison.RG02.Order Pert.Asymptotics WilsonLimitConstruction
open scoped Classical Topology BigOperators

variable {G:Gauge} {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V]
  (R:Run G) (hG:G.Simple) (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
  (d:LocalFormal.Datum R.family (Stock.census V)) (Q:MS.Land.Prescription B)
  (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (ks:V→ℕ)
  (profile:∀k,k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power)
  (hm:ActualOriginalQInitialInput.start R hG u J A profile≤d.level)
  (hp:(ActualOriginalQPointSetup.request R u J).physicalPeriodLower≤(R.family.S.period d.period).val)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "W" => FundedMatchedPointOpening.colors R hG u J A d Q o μ ks profile hm hp
local notation "I₀" => ActualOriginalQInitialPreparation.input R hG u J A d Q o μ ks
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "g" => regulatorRun R.family (d.level+1) d.period (d.level+1)
local notation "K" => (RunFormalChain.fromRun R).step (d.level+1) d.level d.period (Nat.lt_succ_self _)

theorem received (top:d.cutoff=d.level+1) (ref:ActualOriginalQLayout.referenceLevel R u≤d.level+1)
    (t:TestSpace (J₀).tests) (F:Forest (S).ratio) (tag:(S).Choices)
    (a:fieldDir G (R.family.side d.level d.period) 1) :
    Local.normalized (P) (((I₀).leaf t).density) (S) (Integral.sample g a)=
      Order.unitScale (Bare.realMoment (K) F (W t) tag a g):=by
  have beta:=Local.RealStep.trajectory R.family d.cutoff d.period (d.level+1) R.makes (Nat.succ_le_iff.mpr d.below)
  have positive:=Local.RealStep.coupling_pos R.family (d.level+1) d.period (d.level+1) R.makes le_rfl
  have nonzero:(Integral.office (K) F tag g 0 a:ℂ)≠0:=Complex.ofReal_ne_zero.mpr
    (Integral.office_pos (K) F tag g 0 a positive).ne'
  have birth:=FundedMatchedPointOpening.density R hG u J A d Q o μ ks profile hm hp top ref t
  have witnessed:=WilsonPositionSeparatedProfileMayerInitialThermalTrial.witnessed R hG u J A d Q o μ ks profile hm hp t
  rw [Bare.realMoment,Order.scaled_same _ _ (inv_ne_zero nonzero),witnessed.2.2]
  change unitScale (Actual.Push (S) (P).beta (((I₀).leaf t).density) (Integral.sample g a))=_
  rw [←beta,birth]
  simp only [FundedMatchedPointOpening.material,LocalFormal.Datum.kernel,top]
  have same (N:ℕ) (h:d.level<N) (eq:N=d.level+1):
      Integral.model g 0 (W t) ((RunFormalChain.fromRun R).step N d.level d.period h)=
        Integral.model g 0 (W t) (K):=by subst N;rfl
  rw [same d.cutoff d.below top]

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalPhysical
