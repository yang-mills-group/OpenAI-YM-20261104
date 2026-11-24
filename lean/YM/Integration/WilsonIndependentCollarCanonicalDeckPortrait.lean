import YM.Integration.WilsonIndependentCollarCanonicalWrappedTrial
import YM.Integration.WilsonOriginalCensusFinitePortrait
import YM.Integration.WilsonNeutralTwoPrintPathBoardAngular
import YM.Integration.WilsonNeutralTwoPrintPathBoardAxis

/-! The actual microscopic lifts on a repeated first-edge board and their one
common deck average for the measured kinetic response, at every angular rank. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarCanonicalDeckPortrait
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

open WilsonOlderFreshConnectedBirth WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp
open WilsonOlderFreshConnectedBinding


open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary Stationary
open WilsonOriginalPrimerReceipts WilsonNeutralTwoPrintPathJet
open Primitives.TwoWave AllOrder.Haiku AllOrder.Ink Response PertExtension.Series

open WilsonNeutralTwoPrintPathRoll WilsonOlderFreshConnectedAssembly
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker FVA1Physical FVA1Physical.TwoReset


open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic.Near
open WilsonNeutralTwoPrintPathRead

open WilsonNeutralTwoPrintPathFixed (parcel)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonNeutralTwoPrintPathQuoted (bill)

open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Multi
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathDatedPolynomial (row sheet entry)
open WilsonReceivedCoverGrade (Same)
open FundedMarkedPathSelection (output)

open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead WilsonNeutralTwoPrintPeg
open WilsonNeutralTwoPrintPathPolynomial RegulatorIR.Diagram

open WilsonOriginalCensusFaceSites (binder port pin frill root)
open WilsonOriginalCensusDatedSheets (sideValue)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonReceivedCompactVerseEntrance (submit)
open WilsonNeutralSignedPolynomialRate (read)
open WilsonOriginalRawQReversion (coordinates)
open WilsonNeutralTwoPrintPathFineFiber (seats)
open WilsonNeutralTwoPrintPathBoardSeats (homes)
open WilsonNeutralTwoPrintPathBoxMean (plotted)
open WilsonOriginalCensusDeckMean (mean)
open WilsonOriginalCensusCanonicalPageFold (onFace)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCanonicalSocketSeed (present contact)
open WilsonNeutralTwoPrintPathStart (returned)
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonOriginalFoldedMarkedRightColumn WilsonCoeffUV.Wheel.Address
open FVA1Physical.TwoReset
variable {G:Gauge}{V:Type} [Fintype V][DecidableEq V](R:Run G)(k:V→ℕ){D:V→ℕ}
  (pt:V→Chamber)(seed:(v:V)→Choice R k v)(N i per:ℕ)(live:i<N)
local notation "P" => loose R.family.path.levels i
local notation "κ" => fun v=>contact (D v)
local notation "X₀" => coarse R i per
local notation "F₀" => fine R i per
local notation "forest" => repeatF (step R i per)
local notation "γ" => ratioHigh R.family.path.levels R.metals.O N i
local notation "connected" => WilsonOriginalCensusCanonicalKinetic.connected (h:=D) R k pt seed N i per (forest) (γ)
local notation "T" => returned R k (κ) pt N i (X₀) seed

include live in
theorem held (simple:G.Simple)(y:V → Lattice.Cover)(δ:V→Site (P).L)(S:Finset V)(d:ℕ)(A:Stationary.Link G (X₀)):
    read (coordinates G (X₀)) ((connected) (chartIn (P) y δ) S) d A =
      Complex.ofReal (diagonal (mass k S+d) (fun r z=>touch (present D) S ((T) y δ S d r z))
        ((coordinates G (X₀)) A)):=by
  let M:=WilsonReceivedCanonicalVerseRegister.start R k (κ) pt seed (chartIn (P) y δ)
  have paid:Eu k M:=IndependentSourcePathFamily.legal _ _ (fun j _=>
    WilsonReceivedCanonicalVerseBasis.grade R k (κ) pt j (seed j))
  have posted:=WilsonOriginalCensusFinitePortrait.original R N i per live k (present D) simple M paid (γ) S d A
  rw [WilsonOriginalCensusFiniteForest.original R N i per k M (γ) S] at posted
  rw [WilsonOriginalCensusCanonicalDigit.placed R k pt seed N i per y δ S]
  exact posted

variable {grid f:Side}(sized:f.val=grid.val*(loose R.family.path.levels i).L.val)
  (proj:grid.val∣(coarse R i per).val)(hf:f.val∣(fine R i per).val)(S:Finset V)(o:S)(address:V→Site f)
  (root:Site (coarse R i per))(site:S.erase o.val→Site (coarse R i per))(base:Fin (Pages grid (coarse R i per)))
local notation "δ₀" => fun v=>(Ratio.mk (P).L sized:Ratio grid f).residue (address v)

include live in
theorem original (simple:G.Simple)(tag:(step R i per).Choices)
    (front:(FVA1Physical.TwoReset.page proj (homes (P) sized address o.val) base).val=root)
    (others:∀v:S.erase o.val,splitter proj (site v)=homes (P) sized address v.val)
    (origins:Fin (Pages f (F₀))→V → Lattice.Cover)
    (sited:∀(p:Fin (Pages f (F₀)))(v:V),wrap (F₀) (origins p v)=(FVA1Physical.TwoReset.page (n:=f) (N:=F₀) hf (address v) p).val)
    (d:ℕ)(A:Stationary.Link G grid):
    (Pages grid (X₀):ℂ)⁻¹*∑sheets:S→Fin (Pages f (F₀)),
      read (coordinates G (X₀)) ((connected) (onFace origins S sheets) S) d
        (AllOrder.Ker.convey (coverWin proj) A) =
      ∑r∈range (mass k S+d+1),mean proj (plotted proj S o.val root site
        (fun place=>(T) place (δ₀) S d r) (Complex.ofRealCLM.comp (touch (present D) S))
        (fun z=>∏v:Fin r,((coordinates G grid) A (z v):ℂ))):=by
  have heard (p:S→Fin (Pages f (F₀))):
      (connected) (onFace origins S p) S =
        (connected) (chartIn (P) (seats (P) (step R i per).sizes proj hf S address p o) (δ₀)) S:=by
    apply WilsonIndependentCollarCanonicalWrappedTrial.original R k pt seed N i per live (forest) tag simple
    intro l hl
    rw [onFace,dif_pos hl,sited]
    have places:=WilsonNeutralTwoPrintPathFineFiber.original (P) sized (step R i per).sizes
      proj hf S address p o ⟨l,hl⟩
    simpa only [WilsonNeutralTwoPrintPathFineFiber.fine,dif_pos hl,wrap_lift] using places.symm
  simp_rw [heard,held R k pt seed N i per live simple,WilsonNeutralTwoPrintPathBoardAxis.original]
  exact WilsonNeutralTwoPrintPathBoardAngular.original (P) sized (step R i per).sizes proj hf
    S o address root site base front others (mass k S+d) (fun place r=>(T) place (δ₀) S d r)
    (touch (present D) S) ((coordinates G grid) A)

end YM.Integration.WilsonIndependentCollarCanonicalDeckPortrait
end

