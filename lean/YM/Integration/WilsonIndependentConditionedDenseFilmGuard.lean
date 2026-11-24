import YM.Integration.WilsonIndependentConditionedLocatedFirstPanels
/-! The paid first edge at a selected K site on the original physical window. -/
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedDenseFilmGuard
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
  {f:ℕ}(fine:f≤j+1+1)(site:Sites R (f,per) n)
  (votes:(i:Fin n)→R.family.label (d i))(doseCap:Fin n→ℝ)
  (affordable:∀i,(R.family.labels.level (d i)).coeffSize (votes i)≤doseCap i)
  (mask:(Stock.census (Fin n)).Mode)(paid:∀v,‖present lens v‖≤caps v)
  (nonempty:0<n)(adult:∀i,0<d i)
  (prior:Selection R d mask.val→∀i:ℕ,Config G (R.family.side i per)→Marker.Poly (Stock.census (Fin n)))
local notation "track" => WilsonReceivedChronologicalFixedCellFee.tape draw fine site
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


open WilsonIndependentConditionedLocatedFirstPanels (Price Sold)
local notation "hi" r:max => WilsonCloseCaptureDate.level R.family.S ((WilsonAddressedPublicFirstSites.original R draw φ).choose*r)
local notation "lo" r:max => WilsonReceivedChronologicalFixedCellFee.capture R φ r

theorem original (η:ℝ)(stock:Sold (R:=R) (simple:=simple) (d:=d) (P:=P) (m:=m) (school:=school)
    (day:=day) (old:=old) (live:=live) (lens:=lens) (pt:=pt) (toll:=toll) (classroom:=classroom) (adult:=adult) η)
    (affordable:∀i,(R.family.labels.level (d i)).coeffSize (votes i)≤doseCap i)
    (r:ℝ)(rp:0<r)(rl:(WilsonAddressedPublicFirstSites.original R draw φ).choose*r≤R.family.S.a 0)
    (after:first+1≤hi r)(inside:hi r≤f)(small:8*R.family.S.a f<R.family.S.a (hi r))
    (hit:WilsonCenteredCompactBooking.mass R φ r (f,per) site≠0)
    (rl':WilsonReceivedChronologicalFixedCellFee.factor R φ*r≤R.family.S.a 0)
    (after':first+1≤lo r)(inside':lo r≤f)(small':8*R.family.S.a f<R.family.S.a (lo r))
    {df:ℕ}{frame:Frame G df}(data:SectionData frame)(group:Hol G)(active:first+1≤j):
    Price (R:=R) (simple:=simple) (d:=d) (P:=P) (school:=school) (day:=day) (old:=old) (live:=live)
      (lens:=lens) (pt:=pt) (toll:=toll) (classroom:=classroom) (fine:=fine) (site:=site) (votes:=votes)
      (doseCap:=doseCap) (mask:=mask) (paid:=paid) (adult:=adult) (prior:=prior) m η:=
  stock fine site votes doseCap affordable mask paid prior rp rl after inside small hit rl' after' inside' small'
    data group (le_refl m) (old.trans (Nat.le_succ first)) active

end YM.Integration.WilsonIndependentConditionedDenseFilmGuard
end
