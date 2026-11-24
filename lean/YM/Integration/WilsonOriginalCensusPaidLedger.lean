import YM.Integration.WilsonOriginalCensusFiniteLedger
import YM.Integration.WilsonOriginalCensusFixedBank
import YM.Integration.WilsonOriginalCensusFiledArmada

/-! The single physical sheet on the two funded adjacent files. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusPaidLedger
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
open WilsonThermometerDeclaredSeeds

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
  (x:Wallet (room (Fin n)))(tag:(step R i per).Choices)

open WilsonOriginalCensusDatedMaterial (words mounts)
open WilsonOriginalCensusFaceSites (port)
open WilsonVacuumPreResetDatedDeposit (Issued)
local notation "labels" => Hot (Stock.census (Fin n))
local notation "f" => fine R i per
local notation "roster" => binder (f) (fineSites)
local notation "H" => WilsonReceivedDepositedOrbitalLedger.book R Y lo enrolled N X positive limit width
  (roster) pin (fun _=>subset_univ _) (fun s=>s.property.choose_spec) deep (fineSites) t closed tickets

include active tag in
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
    (choose:∀u:Finset (labels),u.Nonempty→u)(v:Stationary.Link G (coarse R i per)):
    ∑u:Finset (labels),wages (roster) x s.val u *
      @reading G n L.tests (labels) _ (Classical.decEq (labels)) R N i per q d k (previous)
        (fun l:labels=>((roster) l).mode.val) pin (fineSites) t (fun l=>((roster) l).center) choose u v =
      sideValue L κ pt top cells seed x true s.val d ((coordinates G (coarse R i per)) v):=by
  obtain ⟨α,A₀,hs,base,purchase⟩:=earned top finer
  obtain ⟨well,cover⟩:=purchase N valid cells seed
  have bound z s:Same q (output X s N z) ((previous) z s):=by
    rw [written z s]
    intro a ha
    rfl
  have stock:=WilsonOriginalCensusFiledArmada.original record high placed names ink w wage
    horizon occupied slots fit
  obtain ⟨names',ink'⟩:=WilsonOriginalCensusFiledArmada.rebook record book high names ink
  exact WilsonOriginalCensusFiniteLedger.original R N per y L t κ pt top cells seed Y lo
    enrolled X positive limit width deep closed tickets (previous) well hs base cover bound active x tag
    rfl high placed names' ink' stock width legal course live funded starts simple s r d through paid kept choose v

end YM.Integration.WilsonOriginalCensusPaidLedger
end
