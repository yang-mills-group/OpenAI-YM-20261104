import YM.Integration.WilsonIndependentCollarCanonicalDeckPortrait
import YM.Integration.WilsonOriginalCensusCanonicalCofinalReset
import YM.Integration.WilsonOriginalCensusCanonicalOpening
import YM.Integration.WilsonNeutralTwoPrintPathBoardTickets

/-! The absolute central reference positions select the physical child, all
marked copies and the common center for the first original edge. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarCanonicalCofinalSeats
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
open WilsonReceivedDepositedOrbitalIssuedFilter (share)
open WilsonOriginalCensusCanonicalOpening (copyRead)
open WilsonReceivedCanonicalSocketSeed (contact present)
open WilsonOriginalCensusCanonicalTopCopies (origins)
open WilsonOriginalCensusCanonicalPageFold (folded onFace)
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonOriginalFoldedMarkedRightColumn WilsonCoeffUV.Wheel.Address
open WilsonNeutralTwoPrintPathBoardSeats (homes)
open WilsonNeutralTwoPrintPathBoardTickets (ticket used)
open FVA1Physical.TwoReset
variable {G:Gauge}{V:Type} [Fintype V][DecidableEq V](R:Run G)(k:V→ℕ){D:V→ℕ}
  (pt:V→Chamber)(seed:(v:V)→Choice R k v)(N i per:ℕ)(live:i<N)
  (y:V → Lattice.Cover)(cells:Digits R.family.path.levels V)
local notation "P" => loose R.family.path.levels i
local notation "κ" => fun v=>contact (D v)
local notation "grid" => coarse R i per
local notation "step₀" => step R i per

def addresses (v:V):Site (fine R i per):=(step₀).ratio.assemble (wrap (grid) (y v),cells i v)

omit [Fintype V] [DecidableEq V] in
theorem actual (v:V):addresses R i per y cells v=wrap (fine R i per) (chartIn (P) y (cells i) v):=by
  change (step₀).ratio.embed (wrap (grid) (y v))+wrap (fine R i per) (lift (cells i v))=
    wrap (fine R i per) ((P).L.val • y v+lift (cells i v))
  rw [map_add,Ratio.embed_wrap]
  rfl

variable (hd:∀v,0<k v)(σ:ℝ)(b:Covers R.family.path.levels.S i (coarse R i per))
local notation "X₀" => coarse R i b.val
local notation "f₀" => fine R i b.val
local notation "δ₁" => fun l:V=>(Ratio.mk (P).L (step₀).sizes:Ratio (grid) (fine R i per)).residue
    (addresses R i per y cells l)
local notation "O" => origins R k seed hd (addresses R i per y cells) σ (grid) dvd_rfl b
local notation "γ" => ratioHigh R.family.path.levels R.metals.O N i
local notation "connected" => WilsonOriginalCensusCanonicalKinetic.connected (h:=D) R k pt seed N i b.val
    (repeatF (step R i b.val)) (γ)

include live in
theorem original (simple:G.Simple)(tag:(step R i b.val).Choices)
    (S:Finset V)(o:S)(d:ℕ)(A:Stationary.Link G (grid)):
    share R (grid) b *
      read (coordinates G (X₀)) (folded (O) (connected) S) d (AllOrder.Ker.convey (coverWin b.prop) A) =
      ∑r∈range (mass k S+d+1),copyRead R k (κ) pt N i seed cells S o.val d r (grid) (X₀) b.prop
        (y o.val) (fun v:S.erase o.val=>y v.val-y o.val)
        (Complex.ofRealCLM.comp (touch (present D) S))
        (fun z=>∏v:Fin r,((coordinates G (grid)) A (z v):ℂ)):=by
  let addr:=addresses R i per y cells
  let pos:=fun v:S.erase o.val=>y v.val-y o.val
  let addresses₀:=WilsonNeutralTwoPrintPathBoardSeats.homes (P) (step₀).sizes addr
  have parent (l:V):addresses₀ l=wrap (grid) (y l):=by
    change (step₀).ratio.parent ((step₀).ratio.assemble (wrap (grid) (y l),cells i l))=_
    exact Ratio.assemble_parent _ _
  have digits:(δ₁)=cells i:=by
    funext l
    change (step₀).ratio.residue ((step₀).ratio.assemble (wrap (grid) (y l),cells i l))=_
    exact Ratio.assemble_res _ _
  let native:=fun l:S.erase o.val=>wrap (X₀) (y o.val+pos l)
  have first:splitter b.prop (wrap (X₀) (y o.val))=addresses₀ o.val:=
    (Macrame.branch b.prop _).trans (parent _).symm
  have rest (l:S.erase o.val):splitter b.prop (native l)=addresses₀ l.val:=by
    rw [parent]
    change splitter b.prop (wrap (X₀) (y o.val+(y l.val-y o.val)))=_
    rw [add_sub_cancel,Macrame.branch]
  have copies (p:Fin (Pages (fine R i per) (f₀)))(v:V):
      wrap (f₀) ((O) p v)=(FVA1Physical.TwoReset.page (tiled R dvd_rfl b) (addr v) p).val:=by
    exact wrap_lift _
  have held:=WilsonIndependentCollarCanonicalDeckPortrait.original (D:=D) R k pt seed N i b.val live
    (step₀).sizes b.prop (tiled R dvd_rfl b) S o addr (wrap (X₀) (y o.val)) native
    (ticket b.prop _ _ first) simple tag (used b.prop _ _ first) rest (O) copies d A
  change _=∑r∈range (mass k S+d+1),WilsonOriginalCensusDeckMean.mean b.prop
    (WilsonNeutralTwoPrintPathBoxMean.plotted b.prop S o.val (wrap (X₀) (y o.val)) native
      (fun place=>WilsonNeutralTwoPrintPathStart.returned R k (κ) pt N i (X₀) seed place (cells i) S d r)
      (Complex.ofRealCLM.comp (touch (present D) S)) (fun z=>∏v:Fin r,((coordinates G (grid)) A (z v):ℂ)))
  rw [show cells i=(δ₁) from digits.symm]
  rw [←held]
  simp [share,folded,WilsonNeutralSignedPolynomialRate.read]

end YM.Integration.WilsonIndependentCollarCanonicalCofinalSeats
end

