import YM.Integration.WilsonIndependentConditionedLocatedFirstBoundary
import YM.Integration.WilsonOriginalTwoFlatIRSocketRanges
/-! The complete measured capture difference on the selected original rows for arbitrary top votes and live sites. -/
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedDenseFilmCapture
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
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonReceivedCanonicalVersePortfolio (weight)
open WilsonOriginalTwoFlatIRCapturedCross (Quote)
open Planned.GuardedAtom Extra.Histories Next.Foundations RG16 RG16.Literal Trace.Physical.GermGraph
local notation "K₀" => j+1+1
local notation "mb" => old.trans (Nat.le_succ first)
local notation "amount" => fun q:Selection R d mask.val=>wt q
local notation "rows_" => fun q:Selection R d mask.val=>row₀ q
local notation "gates" c:max => WilsonOriginalCensusPublicationClock.Open R simple d (ask).school.pieces
  ((ask).school.order+1) (ask).load c
include affordable in
theorem original (r:ℝ)(rp:0 < r)(small:factor R φ*r ≤ R.family.S.a 0)
    (atCapture:first+1 < capture R φ r)(born:capture R φ r ≤ f)(narrow:8*R.family.S.a f < R.family.S.a (capture R φ r))
    (occurs:WilsonCenteredCompactBooking.mass R φ r (f,per) site≠0)
    (young:capture R φ r<K₀-1)(big:2≤R.alloy.B.a.clock.hatBeta (capture R φ r))(licensed:gates (capture R φ r))
    (clocked:(eventually_atTop.mp (WilsonOriginalTwoFlatIRRows.nextClock R simple)).choose≤capture R φ r)
    {p depth E₀:ℕ}(quote:Quote R N per m (first+1) (capture R φ r) p depth ((mb).trans atCapture.le) atCapture.le)
    {C:ℝ}(cp:1≤C)(allowed:allowance≤1)(rent:0≤rate)
    (out:rate≤C*(3*(gAt (capture R φ r))⁻¹)^E₀)(cap:∀a,caps a≤C*(3*(gAt (capture R φ r))⁻¹)^E₀)
    {α:ℝ}(strip:(R.family.path.rep N per (capture R φ r)).p.supportExponent≤α)
    (ou:Opened R.family 0 m per)(ov:Opened R.family 0 (first+1) per)
    (reach:4*(p+(WilsonOriginalTwoFlatIRHalo.power mask.val.card ((∑a,d a)+1+2+(2+2*n*E₀))+0+2))≤depth):
    ‖WilsonOriginalTwoFlatIRSocketBoundary.shift R (N:=N) (amount) (rows_) mask (mb) atCapture‖≤
      (due)*(WilsonOriginalTwoFlatIRSocketRose.charge R d zeroFee P C α E₀ mask*(gAt (capture R φ r))^p):=by
  let a:=capture R φ r-1
  have which:a+1=capture R φ r:=by dsimp [a];omega
  let cost:=WilsonOriginalTwoFlatIRSocketRose.charge R d zeroFee P C α E₀ mask*(gAt (capture R φ r))^p
  have certified (q:Selection R d mask.val):
      ‖reading R (N:=N) (fun U=>((row₀ q) (capture R φ r) U).part mask) m ((mb).trans atCapture.le)-
        reading R (N:=N) (fun U=>((row₀ q) (capture R φ r) U).part mask) (first+1) atCapture.le‖≤cost:=by
    have move {F:ℕ → Prop} (h:F (capture R φ r)):F (a+1):=Eq.mp (congrArg F which.symm) h
    let quotesAt (dayIdx : ℕ) : Prop := ∀ mu : m ≤ dayIdx, ∀ vu : first + 1 ≤ dayIdx,
      Quote R N per m (first+1) dayIdx p depth mu vu
    have quoted:quotesAt (capture R φ r):=fun _ _=>@quote
    have quoteAt:quotesAt (a+1):=move quoted
    have quote₀:Quote R N per m (first+1) (a+1) p depth (by omega) (by omega):=@quoteAt _ _
    have earned:=WilsonOriginalTwoFlatIRSocketVisit.original (R:=R) (per:=per) (V:=V) (draw:=draw)
      (rate:=rate) (allowance:=allowance) (power:=zeroFee) (P:=P) (house:=school) (day:=day) (κ:=fun i=>contact (lens i)) (pt:=pt)
      (top:=K₀) (first:=first) (valid:=live) (toll:=toll) (old:=old) (test:=present lens) (classroom:=classroom)
      (fine:=fine) (z:=site) (s:=mask) (q:=q) (paid:=paid) (hd:=adult) (background:=prior q) (σ:=scale)
      (j:=a) (p:=p) (depth:=depth) (E:=E₀) (α:=α) r rp small (by omega) which.le born (by omega) narrow occurs (by simpa only [which] using big)
      (by simpa only [which] using licensed) (by simpa only [which] using clocked) (by omega) (by omega) quote₀
      cp allowed rent (by simpa only [which] using out) (by simpa only [which] using cap)
      (move (F:=fun i=>(R.family.path.rep N per i).p.supportExponent≤α) strip) ou ov reach
    let earnedAt (i:ℕ):Prop:=∀ h : m ≤ i, ∀ k : first + 1 ≤ i,
      ‖reading R (N:=N) (fun U=>((row₀ q) i U).part mask) m h-
        reading R (N:=N) (fun U=>((row₀ q) i U).part mask) (first+1) k‖≤
        WilsonOriginalTwoFlatIRSocketRose.charge R d zeroFee P C α E₀ mask*(gAt i)^p
    have saved:earnedAt (a+1):=fun _ _=>earned.2.2
    have actual:earnedAt (capture R φ r):=Eq.mp (congrArg earnedAt which) saved
    exact actual _ _
  have span:=WilsonOriginalTwoFlatIRSocketBoundary.shifted R (N:=N) (amount) (rows_) mask (mb) atCapture (fun _=>cost) certified
  have purse:=WilsonReceivedCanonicalVersePortfolio.priced R d N per K₀ live votes mask.val doseCap (fun i _=>affordable i)
  have pos:0≤cost:=(norm_nonneg _).trans (certified (fun _=>Sum.inl ()))
  apply span.trans
  rw [←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right purse pos

end YM.Integration.WilsonIndependentConditionedDenseFilmCapture
end
