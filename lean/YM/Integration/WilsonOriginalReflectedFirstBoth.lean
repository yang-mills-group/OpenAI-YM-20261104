import YM.Integration.WilsonReceivedChronologicalFixedRoseBothFees
import YM.Integration.WilsonOriginalReflectedFirstBoundary

/-! Both signed first and last Wilson fees on the same placed, positive, finite two-preparation roster. -/
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalReflectedFirstBoth
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
variable {G:Gauge}(R:Run G)(simple:G.Simple){n m j N per:ℕ}{schedule:WilsonOriginalAllOrderCourse.Schedule G}
  (d:Fin n→ℕ)(P:ℕ)
local notation "zeroFee" => (fun _ : Fin n=>(0:ℕ))
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
  (day:Day (WilsonOriginalOpticalSchedule.prepared schedule) R simple (programme d (fun _:Fin n=>0) P).school m N)
  {first:ℕ}(old:m≤first)(early:first≤j)(live:j+1+1≤N)
  {V:Realm G ((terms d (fun _:Fin n=>0) P).order+1) Credit.leanC}{draw:V.draws=R.family.path.levels}
  {rate allowance:ℝ}(lens:Fin n→ℕ)(pt:Fin n→Chamber)
  (toll:ℕ→Fin n→ℝ){φ:Test n}{caps:Fin n→ℝ}{A promised:ℕ}{θ:ℝ}
  (classroom:Purchased (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance)
    (fun _:Fin n=>0) P school day (fun i=>contact (lens i)) pt (j+1+1) first live toll old φ caps A promised θ)
  {f requested sourcePole names:ℕ}{B:ℝ}(fine:f≤j+1+1)
  (panel:WilsonMeasuredPublicEntrancePanel.Panel R d N per f (j+1+1) fine live requested sourcePole names B)
  (file:WilsonMovingForkHeterogeneousCut.Filed R d (j+1+1))
  (station:panel.slot=file.station)(axes:panel.axis=file.A N per)
  (mask:(Stock.census (Fin n)).Mode)(paid:∀v,‖present lens v‖≤caps v)
  (nonempty:0<n)(adult:∀i,0<d i)
  (prior:Selection R d mask.val→∀i:ℕ,Config G (R.family.side i per)→Marker.Poly (Stock.census (Fin n)))
local notation "track" => WilsonReceivedChronologicalFixedCellFee.tape draw fine panel.loc
local notation "cells" => onLevels draw (track)
local notation "spots" => WilsonReceivedChronologicalMaterialLine.homes (track) (0:Fin n→Lattice.Cover) first (j-first)
local notation "seed" a:max => WilsonReceivedChronologicalSocket.extend R d mask.val a
local notation "wallet₀" => WilsonReceivedChronologicalSocket.lit (V:=Fin n)
local notation "o" => WilsonIndependentCollarCanonicalCofinalSeats.addresses R (j+1) per (spots) (cells)
local notation "clock" => R.alloy.B.a.clock
local notation "Hhat" => (clock).hatBeta (j+1)
local notation "sideₗ" => coarse R (j+1) per
local notation "lowOrder" => (ask).order
local notation "lowShelf" => (ask).shelf
local notation "σₗ" => Poetry.Agenda.seed (roots semester R simple) MintClock.splits (Burn.horizon (ask).vac) ((clock).J (j+1))
local notation "scale" => Poetry.Agenda.seed (roots semester R simple) MintClock.splits (Burn.horizon (ask).vac) ((clock).J (j+1+1))
local notation "marks" => Stock.census (Fin n)
local notation "bound" => max ((2:ℝ)^((ask).order+(ask).shelf+1)) ((2:ℝ)^(lowOrder+lowShelf+1))
local notation "charges" => fun _:Fin n=>4
local notation "rk" => (∑v:Fin n,d v)+1
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
local notation "extent₀" => WilsonAddressedPublicFirstExtent.extent V.draws (0:Fin n → Lattice.Cover) first (j-first)
local notation "publication" => WilsonAddressedPublicFirstPeriod.appointment R simple d lens pt (charges) tube
  (ask).order lowOrder target precision seller fund (WilsonAddressedPublicFirstRanks.original d P).2.2.2.1
local notation "mult₀" => (WilsonAddressedPublicFirstSites.original R draw φ).choose
local notation "capture₀" r:max => WilsonCloseCaptureDate.level R.family.S ((mult₀)*r)
include station axes early in
theorem original {tol:ℝ}{A u e:ℕ}(ep:0<θ)(tp:0<tol)
    (authorized:WilsonOriginalReflectedFirstTerms.At R simple d P (2*A) tol θ tp ep (first+1) j)
    (activated:WilsonOriginalCensusCanonicalAppointedClock.opening R simple seller fund history (Burn.horizon (ask).vac) ≤ m)
    (ranked:WilsonAddressedPublicFirstOrigin.ceiling R d ≤ (capital).order)
    {r:ℝ}(rp:0<r)(small:(mult₀)*r ≤ R.family.S.a 0)
    (before:first+1 ≤ capture₀ r)(between:capture₀ r ≤ f)(narrow:8*R.family.S.a f<R.family.S.a (capture₀ r))
    (occurs:WilsonCenteredCompactBooking.mass R φ r (f,per) panel.loc≠0)
    (smallLo:WilsonReceivedChronologicalFixedCellFee.factor R φ*r ≤ R.family.S.a 0)
    (floorLo:first+1 ≤ WilsonReceivedChronologicalFixedCellFee.capture R φ r)
    (withinLo:WilsonReceivedChronologicalFixedCellFee.capture R φ r ≤ f)
    (narrowLo:8*R.family.S.a f<R.family.S.a (WilsonReceivedChronologicalFixedCellFee.capture R φ r))
    (front : (t:Multi.Hot (marks)) → t.val.val)
    {I₀:Type}[Fintype I₀]{courseDepth pieces₀ k₀:ℕ}{pole:Bool → ℕ}{span:I₀ → ℕ}{lag:I₀ → Bool → ℕ}
    (faculty:WilsonIndependentCollarDatedTeachers.At schedule R simple V lens d (Burn.horizon (ask).vac)
      courseDepth allowance tube pieces₀ k₀ pole span lag j)(venue:V.anchor ≤ j+1)
    (go:(publication).first ≤ j+1)(board:(publication).period (j+1) (extent₀) ≤ per)
    (floorOld:WilsonSingleHardRadius.first R simple ≤ m)(oldEar:m ≤ u)(ue:u ≤ e)(eb:e ≤ first+1)(fj:first+1 ≤ j)
    (geo:R.family.S.a (first+1)/R.family.S.a (j+1+1) ≤ (R.family.path.levels.clock.hatBeta (first+1))^(2*A))
    (support:∀i,(R.family.path.levels.budget i).supportExponent=100)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G)
    {goal:ℕ}(promise:promised=goal+2*sourcePole*3)
    {oldPrice:Credit}{Z₀:ℕ→ SeriesA G}(quiet:WilsonOriginalCensusFiledAttendance.QuietAt day oldPrice Z₀)
    (basalTeacher:WilsonIndependentCollarDatedTeachers.At schedule R simple V lens d (Burn.horizon (ask).vac)
      courseDepth allowance tube pieces₀ k₀ pole span lag first)
    (basalAnchor:V.anchor≤first+1)
    (sparse:WilsonOriginalCensusSparseRosterOpening.first R simple tube d d (WilsonReceivedChronologicalFixedReserve.charges zeroFee)
      (capital).order (capital).order (capital).target (capital).precision (capital).enough≤first+1)
    (period:WilsonReceivedChronologicalFixedPorts.Period (R:=R) (per:=per) (V:=V) (grades:=d)
      zeroFee P (fun i=>contact (lens i)) pt (j+1+1) first caps)
    (forest:(u:Covers R.family.path.levels.S (first+1) (coarse R (first+1) per))→ Forest (step R (first+1) u.val).ratio)
    (chosen:(u:Covers R.family.path.levels.S (first+1) (coarse R (first+1) per))→ (step R (first+1) u.val).Choices)
    (current:WilsonOriginalOneArmCurrentClock.first R simple d zeroFee P (2*A) tol θ tp ep nonempty≤first):
    ‖WilsonOriginalTwoFlatIRSocketBoundary.last R (N:=N) (b:=first+1)
      (fun q:Selection R d mask.val=>wt q) (fun q=>row₀ q) mask‖ ≤
      (due)*(WilsonOriginalOneArmClearCash.wage mask P θ*(gAt (first+1))^P) ∧
    ‖WilsonOriginalTwoFlatIRSocketBoundary.first R (N:=N) (K:=j+1+1) (u:=e)
      (fun q:Selection R d mask.val=>wt q) (fun q=>row₀ q) mask‖ ≤
      (due)*(WilsonReceivedChronologicalLastFlat.wage mask P 1 θ*(gAt (first+1))^P):=by
  subst promised
  refine ⟨?_,?_⟩
  · exact WilsonReceivedChronologicalFixedRoseCurrentFee.original
      (G:=G) (n:=n) (grades:=d) (R:=R) (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance)
      (power:=zeroFee) (P:=P) (house:=school) (day:=day) (κ:=fun i=>contact (lens i)) (pt:=pt)
      (top:=j+1+1) (first:=first) (valid:=live) (toll:=toll) (old:=old) (test:=present lens)
      (classroom:=classroom) (fine:=fine) (panel:=panel) (file:=file) (s:=mask) (testCap:=paid) (hd:=adult)
      (prior:=prior) (σ:=fun _=>scale) quiet tube (fun t=>(front t).val) (fun t=>(front t).property) basalTeacher basalAnchor sparse period forest chosen
      section_ group (by omega) nonempty (2*A) tol tp ep current geo support station axes
  · exact WilsonOriginalReflectedFirstBoundary.original
      (R:=R) (simple:=simple) (d:=d) (P:=P) (school:=school) (day:=day) (old:=old) (early:=early) (live:=live)
      (lens:=lens) (pt:=pt) (toll:=toll) (classroom:=classroom) (fine:=fine) (panel:=panel) (file:=file)
      (station:=station) (axes:=axes) (mask:=mask) (paid:=paid) (nonempty:=nonempty) (adult:=adult) (prior:=prior)
      (seller:=seller) (fund:=fund) (history:=history) (tube:=tube) ep tp authorized activated ranked
      rp small before between narrow occurs smallLo floorLo withinLo narrowLo front faculty venue go board
      floorOld oldEar ue eb fj geo support section_ group

end YM.Integration.WilsonOriginalReflectedFirstBoth
end
