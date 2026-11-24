import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogPhysical
import YM.Integration.WilsonInitialPrescribedVacuum
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogPrescription
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


theorem funded (camp:Campaign R) (top:d.cutoff=d.level+1)
    (ref:ActualOriginalQLayout.referenceLevel R u≤d.level+1)
    (t:TestSpace (J₀).tests) (F:Forest (S).ratio) (tag:(S).Choices)
    (a:fieldDir G (R.family.side d.level d.period) 1) (n:ℕ) (hired:n≤J.order):
    let X:=((I₀).leaf t).density
    let Z:=fun _:(S).Choices=>Integral.zone (K) (P).p F g a
    Local.markingError (P) X (K) g F tag ((F₀).colors t) Z a n (Fintype.card V)=
      Local.markingError (P) X (K) g F tag (W t) Z a n (Fintype.card V):=by
  intro X Z
  have receipt:=Local.RealStep.genuine R.family d.cutoff d.period d.level (Y) d.below X ((F₀).colors t)
    F tag a R.makes (WilsonPositionSeparatedProfileMayerInitialMarking.primary R hG u J A d Q o μ ks
      profile hm hp ref t) ((F₀).convention.well t)
    n (Fintype.card V) (fun _=>Finset.card_le_univ _) Z
    (fun _=>(Integral.plausible (K) F (P).p g a).1) (fun _=>Set.Subset.refl _)
  rw [WilsonPositionSeparatedProfileMayerInitialMarking.earned R hG u J A d Q o μ ks
    profile hm hp ref t F tag a n]
  have same:(Bulk.Fk (K) F tag (W t) a n)=(Bulk.Fk (K) F tag ((F₀).colors t) a n):=by
    have move (N:ℕ)(live:d.level<N)(eq:N=d.level+1):
        Bulk.Fk ((Y).step N d.level d.period live) F tag (W t) a n=
          Bulk.Fk ((Y).step N d.level d.period live) F tag ((F₀).colors t) a n:=by
      subst N
      exact WilsonInitialPrescribedVacuum.original R camp hG u J A d Q o μ ks profile hm hp t F tag a hired
    exact move d.cutoff d.below top
  rw [same, receipt.2.2.1]
  abel

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogPrescription
