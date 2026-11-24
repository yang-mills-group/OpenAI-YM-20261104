import YM.Integration.WilsonIndependentConditionedDenseFilmBank
import YM.Integration.WilsonReceivedChronologicalFixedRoseSingle
/-! The original teacher earns every interior measurement at the appointed flat field v. -/
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedDenseFilmSameMonths
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

local notation "votes₀" => votes
local notation "due" => WilsonReceivedCanonicalVersePortfolio.wallet R d
  doseCap mask.val
local notation "wt" v:max => WilsonReceivedCanonicalVersePortfolio.weight R d N per (j+1+1) (votes₀) mask.val v
local notation "row₀" v:max => WilsonReceivedChronologicalFixedSocketLife.line
  (R:=R) (N:=N) (per:=per) (grades:=d) (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance)
  (power:=zeroFee) (P:=P) (house:=school) (day:=day) (κ:=fun i=>contact (lens i)) (pt:=pt)
  (top:=j+1+1) (first:=first) (valid:=live) (toll:=toll) (old:=old) (test:=present lens)
  (classroom:=classroom) (fine:=fine) (z:=site) (s:=mask) (q:=v) (paid:=paid) (hd:=adult)
  (prior:=prior v) (σ:=scale)

open WilsonReceivedChronologicalFixedCellFee (factor capture)
open WilsonReceivedChronologicalLastFlat (wage)
open WilsonReceivedChronologicalMaterialCapture (placed)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonReceivedChronologicalFixedCohortFee (Earned)
open WilsonReceivedCanonicalVersePortfolio (weight)
open WilsonIndependentConditionedDenseFilmBank (upper)
open Extra.Histories Extra.Trajectories Extra.Multi
local notation "v₀" => first+1
local notation "K₀" => j+1+1
local notation "walletAt" => (due)
local notation "tuition" => (4*((2*A:ℕ):ℝ)/Real.log 3)*wage mask P 1 θ*(gAt (first+1))^promised

include affordable in
theorem original (r:ℝ)(rp:0<r)(small:factor R φ*r≤R.family.S.a 0)(atCapture:first+1<capture R φ r)
    (born:capture R φ r≤f)(narrow:8*R.family.S.a f<R.family.S.a (capture R φ r))
    (occurs:WilsonCenteredCompactBooking.mass R φ r (f,per) site≠0)
    (forests:∀(j:ℕ)(u:Covers R.family.path.levels.S (j+1) (coarse R (j+1) per)),Forest (step R (j+1) u.val).ratio)
    (chosen:∀(j:ℕ)(u:Covers R.family.path.levels.S (j+1) (coarse R (j+1) per)),(step R (j+1) u.val).Choices)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G)(before:capture R φ r<K₀):
    ‖actualTransport R.family (N:=N) (upper R d (N:=N) fine site votes mask) ((le_refl (first+1)).trans
      (atCapture.le.trans before.le)) 1-
      ∑q:Selection R d mask.val,(wt q)*WilsonReceivedChronologicalFixedRoseBoundary.lower R (N:=N) (K:=K₀)
        (row₀ q) mask (le_refl (first+1)) atCapture‖≤walletAt*(tuition):=by
  let v:=first+1
  let c:=capture R φ r
  let which:=WilsonReceivedChronologicalLedger.stop v v c
  have hire (q:Selection R d mask.val):Earned (power:=zeroFee) (P:=P) (house:=school) (day:=day) (top:=K₀)
      (rows:=row₀ q) m v promised (2*A) θ:=
    WilsonReceivedChronologicalFixedSocketLife.fees (G:=G) (n:=n) (N:=N) (grades:=d) (dims:=lens) (R:=R) (per:=per) (V:=V) (draw:=draw)
    (rate:=rate) (allowance:=allowance) (power:=zeroFee) (P:=P) (house:=school) (day:=day)
    (κ:=fun i=>contact (lens i)) (pt:=pt) (top:=j+1+1) (first:=first) (valid:=live)
    (toll:=toll) (old:=old) (classroom:=classroom) (fine:=fine) (z:=site)
      (s:=mask) (q:=q) (test:=present lens) (paid:=paid) (hd:=adult) (prior:=prior q) (σ:=scale)
      (r:=r) rp small atCapture.le born narrow occurs forests chosen section_ group
  have sold:=WilsonReceivedChronologicalFixedBasisFare.original (R:=R) (N:=N) (per:=per)
    (grades:=d) (power:=zeroFee) (P:=P) (house:=school) (day:=day) (top:=K₀) (valid:=live)
    (s:=mask) (bank:=fun q=>row₀ q) (v:=votes) m v promised (2*A) θ which
    (fun i _=>by
      have scope:=WilsonReceivedChronologicalLedger.scope (le_refl v) c i
      exact ⟨(old.trans (Nat.le_succ first)).trans scope.1,scope.2⟩)
    hire doseCap (fun i _=>affordable i)
  have entered:=WilsonIndependentConditionedDenseFilmBank.arrival (R:=R) (simple:=simple) (d:=d) (P:=P) (school:=school) (day:=day) (old:=old) (live:=live)
    (lens:=lens) (pt:=pt) (toll:=toll) (classroom:=classroom) (fine:=fine)
    (site:=site) (votes:=votes) (mask:=mask) (paid:=paid) (adult:=adult) (prior:=prior)
    ((le_refl (first+1)).trans (atCapture.le.trans before.le))
  have allDates:=WilsonIndependentConditionedDenseFilmBank.integrable (R:=R) (simple:=simple) (d:=d) (P:=P) (school:=school) (day:=day) (old:=old) (live:=live)
    (lens:=lens) (pt:=pt) (toll:=toll) (classroom:=classroom)
    (fine:=fine) (site:=site) (mask:=mask) (paid:=paid) (adult:=adult) (prior:=prior)
  have bill:=WilsonReceivedChronologicalFixedRoseBoundary.charged R mask (fun q=>row₀ q)
    (fun q:Selection R d mask.val=>wt q) (le_refl (first+1)) atCapture before live
    allDates (actualTransport R.family (N:=N) (upper R d (N:=N) fine site votes mask)
      ((le_refl (first+1)).trans (atCapture.le.trans before.le)) 1) (arrival:=0) (by rw [entered,sub_self,norm_zero]) sold.2
  simpa only [zero_add] using bill

end YM.Integration.WilsonIndependentConditionedDenseFilmSameMonths
end
