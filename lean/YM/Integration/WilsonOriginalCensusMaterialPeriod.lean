import YM.Integration.WilsonOriginalCensusWholePeriod
import YM.Integration.WilsonOriginalCensusPaidLedger
import YM.Integration.WilsonIndependentCollarOrbitShapes

/-! One original high source and its independently registered lower on the actual physical board. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusMaterialPeriod
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary QuadraticLocal.Affinity
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetStationaryChange WilsonOriginalPrimerReplicatedInk PhysicalForestMarkedRay PhysicalForestRay
open FreeResolvent WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonOriginalPointCompactRoster WilsonOriginalThreeCopiedCharts
open scoped Classical BigOperators ContDiff Topology
open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalThreePurchasedRays (prescribed)
attribute [local instance] Gauge.frobInner
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet WilsonOriginalCensusCopySlate
open WilsonOlderFreshGraphSlate (Copy)
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology

open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathJet (diagonal)
open WilsonOriginalCensusDatedMaterial (Material charts)
open WilsonReceivedDepositedOrbitalPages (offered)
open WilsonReceivedDepositedOrbitalPrint (front)
open WilsonReceivedCompactVerseEntrance
open WilsonReceivedCoverGrade (Same)
open WilsonOriginalCensusFaceSites (binder pin)
open WilsonReceivedDepositedSocketRows (entered)
open WilsonOriginalCensusDatedMaterial (charts)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open OriginalMarkedSourceComet
open WilsonOriginalCensusDatedSheets (sideValue)
open WilsonOriginalCensusFaceSheet (Addressed)
open WilsonOriginalRawQReversion (coordinates)
open AllOrder AllOrder.Floe QuadraticLocal QuadraticLocal.Rebirth
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonThermometerDeclaredSeeds
open WilsonCoeffUV.Bank.Carp
open WilsonNeutralTwoPrintPathItinerary

open WilsonReceivedDepositedOrbitalNamedWage (wages)
open WilsonReceivedDepositedOrbitalNameWages (central)
open WilsonReceivedDepositedOrbitalFixedMoments (program)

variable {G:Gauge}{n q i:ℕ}{k:Fin n→ℕ}{A δ σ σₗ:ℝ}
  (R:Run G)(N per:ℕ)(y:Fin n → Cover)(L:Material R N i q k σₗ (binder (coarse R i per) y))
  (t:Case L.tests)(κ:(v:Fin n)→Knob (L.tests v))(pt:Fin n→Chamber)(top:ℕ)
  (cells:Digits R.family.path.levels (Fin n))(seed:(v:Fin n)→Choice R k v)
  (Y:Realm G (q+1) Credit.leanC)(lo:Y.anchor ≤ i+1)(enrolled:Paid R Y lo L.tests k δ σ)
  (X:Input Y lo univ k L.tests A)(positive:0≤A)(limit:i+1<N)(width:0<σ)
  (deep:∀s:Hot (Stock.census (Fin n)),0 < mass k s.val.val)
  (closed:Cloze L.tests k Y Credit.leanC)(tickets:Insure n (mass k univ) Y Credit.leanC)
local notation "P" => loose R.family.path.levels i
local notation "fineSites" => chartIn (P) y (cells i)
local notation "previous" => fixed R k κ pt N top (i+1) cells seed
open WilsonOriginalCensusFiniteLedger (reading)
variable (active:Addressed y L t)
  (x:Wallet (room (Fin n)))(tags:(u:Covers R.family.path.levels.S i (coarse R i per))→(step R i u.val).Choices)

open WilsonOriginalCensusDatedMaterial (words mounts)
open WilsonOriginalCensusFaceSites (port)
local notation "labels" => Hot (Stock.census (Fin n))
local notation "f" => fine R i per
local notation "roster" => binder (f) (fineSites)
local notation "H" => WilsonReceivedDepositedOrbitalLedger.book R Y lo enrolled N X positive limit width
  (roster) pin (fun _=>subset_univ _) (fun s=>s.property.choose_spec) deep (fineSites) t closed tickets

open WilsonOriginalCensusDeckMean (mean)
open WilsonCoeffUV.Wheel.Address WilsonIndependentCollarOrbitShapes
open WilsonNeutralTwoPrintPathBoxHome (radius)
open PertExtension.Series AllOrder.Floe

def page (R:Run G)(N i per:ℕ)(hi:i<N){port₀:Passport (fine R i per) (Fin n)}{μ:Type}
    (high:μ→Row port₀ (Stock.census (Fin n)) G (Wallet (room (Fin n))))
    (k:Fin n→ℕ)(x:Wallet (room (Fin n)))(π:Layout G)(Γ:Pace.Coin)(zero:Γ 0=0)
    (e r d:ℕ)(s:(Stock.census (Fin n)).Mode)(v:Stationary.Link G (coarse R i per))
    (u:Covers R.family.path.levels.S i (coarse R i per))(tag:(step R i u.val).Choices):ℂ:=
  let h:(fine R i per).val∣(fine R i u.val).val:=by
    rw [(step R i per).sizes,(step R i u.val).sizes]
    exact Nat.mul_dvd_mul_right u.prop _
  let U:Adjacent.Display (Stationary.Link G (coarse R i u.val)):=fun l b=>
    let raw:=Bulk.Fk (model R N i u.val hi) (repeatF (step R i u.val)) tag
      (copyColor h high k (fun a=>(high a).paint x) π (Step.tape (e+2))) (Stationary.arm G _ 1 b) r
    (Order.observe (Stock.census (Fin n)) r (Order.logMarked raw) l).part s
  (Pages (coarse R i per) (coarse R i u.val):ℂ)⁻¹*Adjacent.born U ((Rebirth.caliber Γ zero).back (e+2)) 0 r d
    (AllOrder.Ker.convey (coverWin u.prop) v)

private theorem originalParent (s:labels):(step R i per).ratio.parent ((roster) s).center=wrap (coarse R i per) (y (pin s)):=by
  let rho:Ratio (coarse R i per) (fine R i per):=(step R i per).ratio
  have put:wrap (fine R i per) ((fineSites) (pin s))=
      rho.assemble (wrap (coarse R i per) (y (pin s)),cells i (pin s)):=by
    change wrap (fine R i per) ((P).L.val•y (pin s)+lift (cells i (pin s)))=
      rho.embed (wrap (coarse R i per) (y (pin s)))+wrap (fine R i per) (lift (cells i (pin s)))
    rw [map_add,rho.embed_wrap]
    rfl
  rw [WilsonOriginalCensusFaceSites.center]
  change rho.parent (wrap (fine R i per) ((fineSites) (pin s)))=_
  rw [put,rho.assemble_parent]

include active tags in
theorem original (earned:WilsonOriginalCensusFixedBank.Income (k:=k) R κ pt q i)
    (finer:i<top)(valid:top ≤ N)(written:∀z s,output X s N z=(previous) z s)
    (record:Material R N (i+1) q k σ (roster))(book:record=(H))
    {port':Passport (f) (Fin n)}{μ:Type}
    (high:μ → Row port' (Stock.census (Fin n)) G (Affinity.Wallet (room (Fin n))))
    (placed:port'=port (f) (fineSites))(names:μ=((s:labels)×(words record s).Roster))(ink:HEq high (mounts record))
    (w:Fin n→ℝ)(wage:∀v,0<w v){order seats shelf:ℕ}
    (horizon:q ≤ order)(occupied:1 ≤ seats)(slots:n ≤ seats)(fit:(∑v,k v) ≤ shelf)
    {start e:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (legal:Legal (Step.tape (e+2)) (π (i+1)))
    (course:Read R N start e Z π Γ)(live:start ≤ i){τ cash:ℝ}
    (funded:Issued R N (i+1) e (Z (i+1)) τ cash)(starts:Γ i 0=0)(simple:G.Simple)
    (s:Hot (Stock.census (Fin n)))(r d:ℕ)(through:r≤q)(paid:r≤e+2)(kept:d≤r)
    (choose:∀u:Finset (labels),u.Nonempty→u)(v:Stationary.Link G (coarse R i per))(unit:‖v‖≤1)
    (C:Fin n→ℝ)(inCash:∀a,‖t a‖≤C a)(ε:ℝ)(ep:0≤ε)
    (opening:@WilsonOriginalCensusRosterOpening.opening G n L.tests (labels) _ (Classical.decEq (labels)) R κ pt k C i top q per
      (Fintype.card (labels)*mass k univ+q) (2*((univ:Finset (Fin n)).image y).sup radius) ε):

    let F:=coverFilter R.family.path.levels.S i (coarse R i per)
    let trial:=fun u=>page R N i per (by omega) high k x (π (i+1)) (Γ i) starts e r d s.val v u (tags u)
    Tendsto trial F (𝓝 (limUnder F trial)) ∧
      ‖limUnder F trial-sideValue L κ pt top cells seed x true s.val d ((coordinates G (coarse R i per)) v)‖ ≤
        (∑s':Finset (labels),‖wages (roster) x s.val s'‖)*((Fintype.card (labels)*mass k univ+q+1:ℕ)*ε):=by
  intro F trial
  letI : DecidableEq (labels):=Classical.decEq _
  obtain ⟨α,A₀,hs,base,purchase⟩:=earned top finer
  obtain ⟨well,cover⟩:=purchase N valid cells seed
  have bound z s:Same q (output X s N z) ((previous) z s):=by
    rw [written z s]; intro a ha; rfl
  have stock:=WilsonOriginalCensusFiledArmada.original record high placed names ink w wage horizon occupied slots fit
  obtain ⟨names',ink'⟩:=WilsonOriginalCensusFiledArmada.rebook record book high names ink
  have geometry (J:Finset (labels))(o:J):WilsonNeutralTwoPrintPathBoxHome.breadth J o.val 0
      (WilsonIndependentCollarOrbitalReception.relative J o.val (fun l:labels=>y (pin l)))≤
      2*((univ:Finset (Fin n)).image y).sup radius:=by
    apply WilsonIndependentCollarOrbitShapes.prepaid _ J o _ 0
    intro l _
    simpa only [sub_zero] using mem_image_of_mem y (mem_univ (pin l))
  have heard:=WilsonOriginalCensusWholePeriod.original R Y lo enrolled N X positive limit width per (roster) pin
    (fun _=>subset_univ _) (fun l=>l.property.choose_spec) deep (fineSites) t closed tickets (previous) well hs base
    cover bound high placed names' ink' stock width tags choose x legal course live funded starts r d through paid kept
    s.val v unit (fun l:labels=>y (pin l)) (fun l=>(originalParent R per y cells l).symm) κ pt top valid cells seed
    rfl _ geometry C inCash ε ep simple opening
  have onSheet:=WilsonOriginalCensusPaidLedger.original R N per y L t κ pt top cells seed Y lo enrolled X positive
    limit width deep closed tickets active x (tags ⟨per,dvd_rfl⟩) earned finer valid written record book high placed
    names ink w wage horizon occupied slots fit legal course live funded starts simple s r d through paid kept choose v
  refine ⟨heard.1,?_⟩
  rw [←onSheet]
  exact heard.2

end YM.Integration.WilsonOriginalCensusMaterialPeriod
end
