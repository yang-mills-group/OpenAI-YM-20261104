import YM.Integration.WilsonReceivedChronologicalFixedRoseGridFiles
import YM.Integration.WilsonReceivedChronologicalFixedRoseOriginalCell
import YM.Integration.WilsonReceivedChronologicalFixedRoseVariation
import YM.Integration.WilsonReceivedChronologicalFixedRoseTestSource
import YM.Integration.WilsonReceivedChronologicalFixedRoseOriginalEnds
import YM.Integration.WilsonReceivedChronologicalFixedRoseOriginalAccount
import YM.Integration.WilsonReceivedChronologicalFixedRoseBothFees
import YM.Integration.WilsonReceivedChronologicalFixedRoseCurrentFee
import YM.Integration.WilsonAddressedPublicFirstRoseBoundary
/-! Both endpoints of one fitted physical Rose have actual funded returns at the
same panel, with its original earlier law and one deposited stencil salary. -/
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseGridField
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

open WilsonOriginalCensusCanonicalRows WilsonOriginalMixedBlockRows WilsonThermometerDeclaredSeeds
open WilsonOriginalStarSceneWords (rank)
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider OriginalMarkedSourceComet
open Filter MintClock XSpace Pert.Asymptotics

open WilsonVacuumPreResetStationaryChange (step coarse levels)
open WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalMeasuredOccupiedForest (Read)
open WilsonOriginalRawQReversion (coordinates)
open WilsonOriginalCensusCanonicalTopCopies (origins)
open WilsonOriginalCensusCanonicalPageFold (folded)
open WilsonReceivedDepositedOrbitalIssuedFilter (share)
open WilsonNeutralSignedPolynomialRate (read)
open FVA1Physical.TwoReset WilsonCoeffUV.Winding Further.PhysicalPeriodLimitF933 Macrame
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider.Canvas FreeResolvent
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Pressure Precision Tree Exterior PertExtension PertExtension.Series WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open scoped Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner



open Source Labels
open WilsonOriginalFullRosterCouplingClock (work)
open WilsonReceivedChronologicalPanelClock (fare)
open WilsonOriginalOccupiedCorridor (sites)
open WilsonOriginalCensusAttendanceStation (Day)
open WilsonOriginalCensusPhysicalAttendance (roots tab Room)
open WilsonReceivedChronologicalPanelClock (debitDepth fare)
open WilsonOriginalOccupiedWindow WilsonOriginalOccupiedCorridor WilsonOriginalJointTrialHearing
open WilsonOriginalCensusPhysicalAttendance (Room roots tab)
open WilsonOriginalCensusFundedAttendance (Demand)
open WilsonReceivedChronologicalFixedLedger (Registered)
open WilsonReceivedChronologicalFixedEarner (programme)
open WilsonReceivedChronologicalFixedReserve (terms)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonOriginalCensusAttendanceStation
open AllOrder AllOrder.Floe
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonReceivedFixedDigitHistory (Digits)
variable {G:Gauge}(R:Run G)(simple:G.Simple){m j N per:ℕ}{schedule:WilsonOriginalAllOrderCourse.Schedule G}
  (d:Fin 3→ℕ)(P:ℕ)
local notation "zeroFee" => (fun _ : Fin 3=>(0:ℕ))
local notation "semester" => (WilsonOriginalOpticalSchedule.prepared schedule)
local notation "ask" => (programme d (zeroFee) P)
local notation "length" => ((terms d (zeroFee) P).order)
open WilsonNeutralTwoPrintPathBoxHome (breadth)
open WilsonIndependentCollarOrbitalReception (relative)
open WilsonOriginalCensusCanonicalAngularMenu (repeated plottedLow)
open WilsonReceivedCanonicalSocketSeed (contact present)

open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonOriginalCensusFaceSites (binder port)
open WilsonOriginalCensusFaceSheet (Addressed)
open FundedMarkedPathSelection (output)
open WilsonReceivedFixedDigitCanonical (fixed)

open Comparison.Density.Transport
open WilsonOriginalCensusCanonicalFirstEdgePayer (Source)

open WilsonReceivedChronologicalFixedPlaced (Purchased)
open WilsonReceivedChronologicalFixedSocketLife
open WilsonReceivedChronologicalFixedCellFee
open WilsonReceivedChronologicalMaterialCapture (placed)
open WilsonReceivedChronologicalSocket (input)
open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonReceivedChronologicalFixedRoster
open WilsonReceivedChronologicalMaterialLine (homes)
open Function Set Filter MeasureTheory Analysis Table Spec Extraction Next.UVStress
open WilsonReceivedChronologicalMaterialSites
open StressFlux.Matching Cells WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking

variable (school:Room (WilsonOriginalOpticalSchedule.prepared schedule) R simple)
  (day:Day (WilsonOriginalOpticalSchedule.prepared schedule) R simple (programme d (fun _:Fin 3=>0) P).school m N)
  {first:ℕ}(old:m≤first)(early:first≤j)(live:j+1+1≤N)
  {V:Realm G ((terms d (fun _:Fin 3=>0) P).order+1) Credit.leanC}{draw:V.draws=R.family.path.levels}
  {rate allowance:ℝ}(lens:Fin 3→ℕ)(pt:Fin 3→Chamber)
  (toll:ℕ→Fin 3→ℝ){φ:Test 3}{caps:Fin 3→ℝ}{A promised:ℕ}{θ:ℝ}
  (classroom:Purchased (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance)
    (fun _:Fin 3=>0) P school day (fun i=>contact (lens i)) pt (j+1+1) first live toll old φ caps A promised θ)
  {f requested sourcePole names:ℕ}{B:ℝ}(fine:f≤j+1+1)
  (panel:WilsonMeasuredPublicEntrancePanel.Panel R d N per f (j+1+1) fine live requested sourcePole names B)
  (file:WilsonMovingForkHeterogeneousCut.Filed R d (j+1+1))
  (station:panel.slot=file.station)(axes:panel.axis=file.A N per)
  (mask:(Stock.census (Fin 3)).Mode)(paid:∀v,‖present lens v‖≤caps v)
  (role:Fin 3→Fin 3)(roles:d=WilsonAddressedPublicSubmittedDates.grades role)
  (prior:Selection R d mask.val→∀i:ℕ,Config G (R.family.side i per)→Marker.Poly (Stock.census (Fin 3)))
local notation "adult" => (fun i=>roles ▸ WilsonAddressedPublicSubmittedDates.positive role i)
local notation "track" => WilsonReceivedChronologicalFixedCellFee.tape draw fine panel.loc
local notation "cells" => onLevels draw (track)
local notation "spots" => WilsonReceivedChronologicalMaterialLine.homes (track) (0:Fin 3→Lattice.Cover) first (j-first)
local notation "seed" a:max => WilsonReceivedChronologicalSocket.extend R d mask.val a
local notation "wallet₀" => WilsonReceivedChronologicalSocket.lit (V:=Fin 3)
local notation "o" => WilsonIndependentCollarCanonicalCofinalSeats.addresses R (j+1) per (spots) (cells)
local notation "clock" => R.alloy.B.a.clock
local notation "Hhat" => (clock).hatBeta (j+1)
local notation "sideₗ" => coarse R (j+1) per
local notation "lowOrder" => (ask).order
local notation "lowShelf" => (ask).shelf
local notation "σₗ" => Poetry.Agenda.seed (roots semester R simple) MintClock.splits (Burn.horizon (ask).vac) ((clock).J (j+1))
local notation "scale" => Poetry.Agenda.seed (roots semester R simple) MintClock.splits (Burn.horizon (ask).vac) ((clock).J (j+1+1))
local notation "marks" => Stock.census (Fin 3)
local notation "bound" => max ((2:ℝ)^((ask).order+(ask).shelf+1)) ((2:ℝ)^(lowOrder+lowShelf+1))
local notation "charges" => fun _:Fin 3=>4
local notation "rk" => (∑v:Fin 3,d v)+1
local notation "home" => ((Passport.point (o)).coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
local notation "gAt" b:max => Pert.Asymptotics.regulatorRun R.family N per b
local notation "capital" => terms d (zeroFee) P
local notation "rentOrder" => (capital).rent+1
local notation "precision" => (capital).precision
local notation "target" => (capital).target

local notation "votes₀" => WilsonOriginalObservedRoseCorrectedWords.votes R d (N:=N) (per:=per)
  file panel.names panel.turn
local notation "due" => WilsonReceivedCanonicalVersePortfolio.wallet R d
  (fun _=>B*(R.family.path.levels.clock.hatBeta (j+1+1))^sourcePole) mask.val
local notation "wt" v:max => WilsonReceivedCanonicalVersePortfolio.weight R d N per (j+1+1) (votes₀) mask.val v
local notation "row₀" v:max => WilsonReceivedChronologicalFixedRoseCell.bank
  (R:=R) (N:=N) (per:=per) (grades:=d) (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance)
  (power:=zeroFee) (P:=P) (house:=school) (day:=day) (κ:=fun i=>contact (lens i)) (pt:=pt)
  (top:=j+1+1) (first:=first) (valid:=live) (toll:=toll) (old:=old) (test:=present lens)
  (classroom:=classroom) (fine:=fine) (panel:=panel) (s:=mask) (testCap:=paid) (hd:=adult)
  (prior:=prior) (σ:=fun _=>scale) v
open RG16 RG16.Literal
open Extra.Histories Extra.Trajectories Extra.Multi
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonMeasuredPublicEntranceCellWords (physical)
open WilsonMeasuredPublicEntrancePanel (Reading)
open Extra.Trajectories Extra.Multi
variable (seller:ℕ → Gear G → ℝ)(fund:FundedMarkedCoverRows.prices seller R.kit)
  (history:FundedOriginalVacuumPaths.prices R.kit)(tube:LinkTube G)
local notation "extent₀" => WilsonAddressedPublicFirstExtent.extent V.draws (0:Fin 3 → Lattice.Cover) first (j-first)
local notation "publication" => WilsonAddressedPublicFirstPeriod.appointment R simple d lens pt (charges) tube
  (ask).order lowOrder target precision seller fund (WilsonAddressedPublicFirstRanks.original d P).2.2.2.1
local notation "mult₀" => (WilsonAddressedPublicFirstSites.original R draw φ).choose
local notation "capture₀" r:max => WilsonCloseCaptureDate.level R.family.S ((mult₀)*r)
open WilsonOriginalTwoFlatIRCapturedCross (Quote)
open WilsonOriginalTwoFlatIRSocketPower (debt)
open WilsonReceivedChronologicalFixedRoseFittedDebit (written)
local notation "lower" => first+1
local notation "upper" => j+1+1
local notation "captureHere" y:max => WilsonReceivedChronologicalFixedCellFee.capture R φ y
local notation "calendar" k:max => WilsonOriginalCensusPublicationClock.Open R simple d (ask).school.pieces
  ((ask).school.order+1) (ask).load k
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonOlderFreshSoftSocketTotal (normalized)
open WilsonReceivedChronologicalFixedRoseGridFiles (entry)
def path {q K f₀ per₀:ℕ}{X:Realm G (q+1) Credit.leanC}
    (drawing:X.draws=R.family.path.levels)(fK:f₀≤K)
    (site:Fin 3→Lattice.Site (R.family.side f₀ per₀)):Digits R.family.path.levels (Fin 3):=
  WilsonIndependentCollarDatedPrior.onLevels drawing
    (WilsonReceivedChronologicalFixedCellFee.tape (R₀:=R) (per₀:=per₀) (V₀:=X) drawing fK site)
def location {q K f₀ per₀:ℕ}{X:Realm G (q+1) Credit.leanC}
    (drawing:X.draws=R.family.path.levels)(fK:f₀≤K)
    (site:Fin 3→Lattice.Site (R.family.side f₀ per₀))(c first:ℕ):Fin 3→Lattice.Cover:=
  let selected:=WilsonReceivedChronologicalFixedCellFee.tape (R₀:=R) (per₀:=per₀) (V₀:=X) drawing fK site
  WilsonIndependentCollarOrdinaryCruise.address R.family.path.levels
    (path (R:=R) (X:=X) (per₀:=per₀) drawing fK site) (c-(first+1)) (first+1)
    (WilsonReceivedChronologicalMaterialLine.homes (V:=X) selected (0:Fin 3→Lattice.Cover) first (first-first))

def angular (D:Fin 3→ℕ):ℝ:=1+∑s:Finset (Fin 3),‖touch (present D) s‖
theorem salary (D:Fin 3→ℕ){g:ℝ}(gp:0<g)(cold:g≤1)(debt:ℕ):
    1≤angular D ∧ ∀s:Finset (Fin 3),‖touch (present D) s‖≤angular D*(g⁻¹)^debt:=by
  classical
  have one:1≤angular D:=by unfold angular;exact le_add_of_nonneg_right (Finset.sum_nonneg (fun s _=>ContinuousLinearMap.opNorm_nonneg (touch (present D) s)))
  have hot:1≤g⁻¹:=by rw [le_inv_comm₀ (by norm_num) gp,inv_one];exact cold
  refine ⟨one,?_⟩
  intro s
  have within:‖touch (present D) s‖≤∑a:Finset (Fin 3),‖touch (present D) a‖:=
    Finset.single_le_sum (f:=fun a:Finset (Fin 3)=>‖touch (present D) a‖) (fun a _=>ContinuousLinearMap.opNorm_nonneg (touch (present D) a)) (Finset.mem_univ s)
  calc
    _≤angular D:=by unfold angular;linarith
    _≤_:=le_mul_of_one_le_right ((by norm_num : (0:ℝ)≤1).trans one) (one_le_pow₀ hot)

theorem original (r:ℝ)(atCapture:first+1<captureHere r)(born:captureHere r≤f)
    (order p E₀ Q goal E₁:ℕ)(C α C₁:ℝ)(site:Fin 3→Lattice.Site (R.family.side f per))(whereAt:panel.loc=site):
    let data:=entry (simple:=simple) (φ:=φ) (R:=R) (N:=N) (per:=per) (d:=d) (P:=P)
      (school:=school) (day:=day) (old:=old) (live:=live) (lens:=lens) (pt:=pt) (toll:=toll)
      (classroom:=classroom) (fine:=fine) (panel:=panel) (file:=file) (mask:=mask) (paid:=paid)
      (role:=role) (roles:=roles) (prior:=prior)
      r atCapture born order p E₀ Q goal E₁ C α C₁
    data.independent=normalized R d (fun i=>contact (lens i)) pt N per (j+1+1) (captureHere r) (first+1)
      (path (R:=R) (X:=V) (per₀:=per) draw fine site) mask.val
      (votes R d (N:=N) (per:=per) file panel.names panel.turn)
      (location (R:=R) (X:=V) (per₀:=per) draw fine site (captureHere r) first)
      (touch (present lens) mask.val) Q (gAt (first+1)):=by
  subst site
  rfl
end YM.Integration.WilsonReceivedChronologicalFixedRoseGridField
end
