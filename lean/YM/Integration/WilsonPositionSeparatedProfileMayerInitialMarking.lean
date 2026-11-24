import YM.Integration.WilsonPositionSeparatedProfileMayerInitialThermalPhysical
import YM.Integration.ManuscriptQLocalActualLog

/-! The exact normalized connected error on the received genuine Q, with its compensated Wilson vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialMarking
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
local notation "g" => regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "Y" => RunFormalChain.fromRun R
local notation "K" => d.kernel (Y)
local notation "F₀" => ActualOriginalQInitialInput.input R hG u J A d Q o μ ks profile hm hp

include Q o μ ks profile hm hp in
theorem primary (ref:ActualOriginalQLayout.referenceLevel R u≤d.level+1) (t:TestSpace (J₀).tests):
    Actual.Floor (P) (((I₀).leaf t).density):=by
  have equal:((I₀).leaf t).density=ManuscriptQLocalActualLog.source R d (F₀) t:=by
    funext U
    rw [ManuscriptQLocalActualLog.literal, (ActualOriginalQInitialInput.input_fields R hG u J A d Q o μ ks profile hm hp).2.2.2.2.1]
    simpa only [Complex.coe_smul] using
      QLocalNormalizedQBirth.source R hG u J A d Q o μ ks ref t U
  rw [equal]
  exact ManuscriptQLocalActualLog.floor R d (F₀) t

theorem earned (ref:ActualOriginalQLayout.referenceLevel R u≤d.level+1) (t:TestSpace (J₀).tests)
    (F:Forest (S).ratio) (tag:(S).Choices) (a:fieldDir G (R.family.side d.level d.period) 1) (n:ℕ):
    let X:=((I₀).leaf t).density
    let Z:=fun _:(S).Choices=>Integral.zone (K) (P).p F g a
    Local.markingError (P) X (K) g F tag (W t) Z a n (Fintype.card V)=
      Local.cumulant (P) X (S) (Integral.sample g a)-
        Order.value (g:ℂ) (Order.logMarked (Bulk.Fk (K) F tag (W t) a n)):=by
  intro X Z
  have receipt:=Local.RealStep.genuine R.family d.cutoff d.period d.level (Y) d.below X (W t)
    F tag a R.makes (primary R hG u J A d Q o μ ks profile hm hp ref t)
    (FundedMatchedPointOpening.well R hG u J A d Q o μ ks profile hm hp t)
    n (Fintype.card V) (fun _=>Finset.card_le_univ _) Z
    (fun _=>(Integral.plausible (K) F (P).p g a).1) (fun _=>Set.Subset.refl _)
  rw [receipt.2.2.1]
  abel

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialMarking
