import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogRegistered
import YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogCost
import YM.Integration.WilsonPositionSeparatedProfileMayerInitialMarking

/-! The true normalized physical cumulant and its independent compensated full log on one genuine Wilson block. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogPhysical
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

local notation "Kₙ" => (Y).step (d.level+1) d.level d.period (Nat.lt_succ_self _)
local notation "gₙ" => regulatorRun R.family (d.level+1) d.period (d.level+1)
local notation "Γ" => Stock.census V
open WilsonMatrixTicketLanesReportedPrepaid WilsonPositionSeparatedProfileMayerInitialLogCohort
open RGComparison.Core16 RGComparison.Core16.Spool
open Extra.Trajectories (connected)
open Finset

def amount {L:Type} [Fintype L] [DecidableEq L] (n:ℕ) (C:ℝ):ℝ:=
  let m:ℝ:=Fintype.card (Stock.census L).Mode
  (m+1)*Fintype.card L*(1+(n+1:ℝ)*m*C+m)^(Fintype.card L)

theorem priced (paid:Paid G R.kit) (top:d.cutoff=d.level+1)
    (ref:ActualOriginalQLayout.referenceLevel R u≤d.level+1) (t:TestSpace (J₀).tests)
    (F:Forest (S).ratio) (tag:(S).Choices) (a:fieldDir G (R.family.side d.level d.period) 1)
    (cap K₀ q E n:ℕ) (C:ℝ) (cp:0≤C) (reserve:q+E*Fintype.card V≤n) (small:(gₙ)≤1)
    (limits:∀i,ks i≤K₀) (inside:∀i,‖Exterior.collect G a i‖≤(cap:ℝ)+1)
    (degree:∀(s:(Γ).Mode)(z:∀i,WilsonMatrixTicketLanesTerminalQWords.Piece R (roster u s i)),
      Spool.power (WilsonMatrixTicketLanesTerminalQWords.word R (roster u s) z)≤n)
    (window:∀s:(Γ).Mode,Window R Q (roster u s) K₀ cap (q+E*Fintype.card V+1) E n μ C d.level):
    let reader:=WilsonPositionSeparatedProfileMayerInitialThermalWords.reader R hG u J A d Q o μ ks t
    let w:=WilsonPositionSeparatedProfileMayerInitialLogWeights.weight reader
    let X:=((I₀).leaf t).density
    Poly.price w (Local.cumulant (P) X (S) (Integral.sample (gₙ) a)-
        Order.value ((gₙ):ℂ) (Order.logMarked (Bulk.Fk (Kₙ) F tag (W t) a n)))≤
      (gₙ)^(q+1)*amount (L:=V) n C:=by
  classical
  intro reader w X
  let N:=d.level+1
  let U:=Integral.sample (gₙ) a
  let M:=Actual.Push (S) (P).beta X U
  let x:=Bulk.Fk (Kₙ) F tag (W t) a n
  let f:=Order.unitScale (Bare.realMoment (Kₙ) F (W t) tag a (gₙ))
  let m:ℝ:=Fintype.card (Γ).Mode
  have gp:0<(gₙ):=IterationFour.Currency.g_pos R.makes _ _ _ le_rfl
  have wp:=WilsonPositionSeparatedProfileMayerInitialLogWeights.positive reader
  have e₀:unitScale M=f:=WilsonPositionSeparatedProfileMayerInitialThermalPhysical.received
    R hG u J A d Q o μ ks profile hm hp top ref t F tag a
  have vacant:=(Local.RealStep.advance R.family d.cutoff d.period d.level d.below X R.makes
    (WilsonPositionSeparatedProfileMayerInitialMarking.primary R hG u J A d Q o μ ks profile hm hp ref t)).vacancy U
  have no:M.part (Γ).quiet≠0:=by
    rw [show M.part (Γ).quiet=_ from vacant]
    exact Complex.ofReal_ne_zero.mpr
      ((Normal.actual R.family.path R.makes.wilson d.cutoff d.period d.level d.below.le).positive U).ne'
  have registered:=WilsonPositionSeparatedProfileMayerInitialLogRegistered.entered R hG u J A d Q o μ ks
    profile hm hp paid top t F tag a cap K₀ (q+E*Fintype.card V+1) E n C cp limits inside degree window
  have measure:Poly.price w (unitScale M-value ((gₙ):ℂ) (ratio x)) ≤ m*(gₙ)^(q+E*Fintype.card V+1):=by
    rw [e₀]
    refine (Finset.sum_le_sum (s:=Finset.univ) (fun s _=>registered.1 s)).trans_eq ?_
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,m]
  have incoming:WilsonPositionSeparatedProfileMayerInitialLogBill.entire w (render (ratio x))≤
      ((n+1:ℝ)*m*C)/(gₙ)^E:=by
    refine (WilsonPositionSeparatedProfileMayerInitialLogIncome.sum (ratio x) w _ registered.2).trans_eq ?_
    dsimp only [m]
    ring
  exact WilsonPositionSeparatedProfileMayerInitialLogCost.purchased gp small (by positivity) (by positivity)
    (Bulk.fk_unit ..) (Bulk.fk_sym ..) M no w wp incoming reserve measure

theorem error (top:d.cutoff=d.level+1)
    (ref:ActualOriginalQLayout.referenceLevel R u≤d.level+1) (t:TestSpace (J₀).tests)
    (F:Forest (S).ratio) (tag:(S).Choices) (a:fieldDir G (R.family.side d.level d.period) 1) (n:ℕ):
    let X:=((I₀).leaf t).density
    let Z:=fun _:(S).Choices=>Integral.zone (K) (P).p F g a
    Local.markingError (P) X (K) g F tag (W t) Z a n (Fintype.card V)=
      Local.cumulant (P) X (S) (Integral.sample (gₙ) a)-
        Order.value ((gₙ):ℂ) (Order.logMarked (Bulk.Fk (Kₙ) F tag (W t) a n)):=by
  intro X Z
  rw [WilsonPositionSeparatedProfileMayerInitialMarking.earned R hG u J A d Q o μ ks profile hm hp ref t F tag a n]
  have clock:g=(gₙ):=by rw [top]
  rw [clock]
  have same (N:ℕ)(live:d.level<N)(eq:N=d.level+1):
      Bulk.Fk ((Y).step N d.level d.period live) F tag (W t) a n=Bulk.Fk (Kₙ) F tag (W t) a n:=by
    subst N
    rfl
  rw [show Bulk.Fk (K) F tag (W t) a n=_ from same d.cutoff d.below top]

end YM.Integration.WilsonPositionSeparatedProfileMayerInitialLogPhysical
