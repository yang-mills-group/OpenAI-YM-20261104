import YM.Integration.WilsonIndependentConditionedLocatedFirstBoundary
import YM.Integration.WilsonReceivedChronologicalFixedRoseCurrentFee
import YM.Integration.WilsonOriginalTwoFlatIRSocketBoundary
/-! The lower flat edge on the actual common receiver, including all occupied subsets of a fixed K-born stencil. -/
set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedDenseFilmLast
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


open WilsonOriginalCensusFiledAttendance (QuietAt)
open WilsonReceivedCanonicalVersePortfolio (weight)
open Extra.Histories Extra.Trajectories Extra.Multi
open WilsonThermometerUnitFilingFlatTelescope (numerator)
local notation "K₀" => j+1+1
local notation "g₀" => regulatorRun R.family N per (first+1)
local notation "amount" => fun q:Selection R d mask.val=>wt q
local notation "rows_" => fun q:Selection R d mask.val=>row₀ q
include affordable in
theorem original {Z₀:ℕ → SeriesA G}{price:Credit}(quiet:QuietAt day price Z₀)
    {Types:Type}[Fintype Types]{purchased pieces physical:ℕ}{schoolPole:Bool → ℕ}{span:Types → ℕ}{lag:Types → Bool → ℕ}
    (tube:LinkTube G)(front:Multi.Hot (Stock.census (Fin n)) → Fin n)(member:∀t,front t∈t.val.val)
    (faculty:WilsonIndependentCollarDatedTeachers.At schedule R simple V lens d (Burn.horizon (ask).vac)
      purchased allowance tube pieces physical schoolPole span lag first)(anchor:V.anchor ≤ first+1)
    (sparse:WilsonOriginalCensusSparseRosterOpening.first R simple tube d d (WilsonReceivedChronologicalFixedReserve.charges zeroFee)
      (capital).order (capital).order (capital).target (capital).precision (capital).enough ≤ first+1)
    (period:WilsonReceivedChronologicalFixedPorts.Period (R:=R) (per:=per) (V:=V) (grades:=d)
      zeroFee P (fun i=>contact (lens i)) pt K₀ first caps)
    (forest:(u:Covers R.family.path.levels.S (first+1) (coarse R (first+1) per)) → Forest (step R (first+1) u.val).ratio)
    (chosen:(u:Covers R.family.path.levels.S (first+1) (coarse R (first+1) per)) → (step R (first+1) u.val).Choices)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G)
    (active:first+3 ≤ K₀)(np:0<n)(cost:ℕ)(tol:ℝ)(tp:0<tol)(ep:0<θ)
    (current:WilsonOriginalOneArmCurrentClock.first R simple d zeroFee P cost tol θ tp ep np≤first)
    (aperture:R.family.S.a (first+1)/R.family.S.a K₀ ≤ (R.family.path.levels.clock.hatBeta (first+1))^cost)
    (support:∀i,(R.family.path.levels.budget i).supportExponent=100)
    :‖WilsonOriginalTwoFlatIRSocketBoundary.last R (N:=N) (b:=first+1) (amount) (rows_) mask‖≤
      (due)*(WilsonOriginalOneArmClearCash.wage mask P θ*(g₀)^P):=by
  let L:=Selection R d mask.val
  let F:L → ℂ:=fun q=>WilsonOriginalJointTrialHearing.fee R N per (1:Config G (R.family.side (first+1) per))
    (row₀ q) (first+1) mask
  let w:L → ℂ:=weight R d N per K₀ votes mask.val
  let W:=WilsonOriginalOneArmClearCash.wage mask P θ*(g₀)^P
  have currentFee (q:L):‖F q‖≤W:=
    WilsonReceivedChronologicalFixedRoseCurrent.original (G:=G) (n:=n) (N:=N) (grades:=d)
      (dims:=lens) (R:=R) (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=allowance)
      (power:=zeroFee) (P:=P) (house:=school) (day:=day) (κ:=fun i=>contact (lens i)) (pt:=pt) (top:=K₀) (first:=first)
      (valid:=live) (toll:=toll) (old:=old) (test:=present lens) (classroom:=classroom) (fine:=fine)
      (z:=site) (s:=mask) (q:=q) (paid:=paid) (hd:=adult) (prior:=prior q) (σ:=scale)
      quiet tube front member faculty anchor sparse period forest chosen section_ group active np cost tol tp ep current aperture support
  have cash:=WilsonReceivedCanonicalVersePortfolio.priced R d N per K₀ live votes mask.val doseCap (fun i _=>affordable i)
  have nonneg:0≤W:=(norm_nonneg (F (fun _=>Sum.inl ()))).trans (currentFee _)
  change ‖∑q:L,w q*F q‖≤(due)*W
  calc
    _ ≤ ∑q:L,‖w q*F q‖:=norm_sum_le _ _
    _ ≤ ∑q:L,‖w q‖*W:=sum_le_sum (fun q _=>by rw [norm_mul];exact mul_le_mul_of_nonneg_left (currentFee q) (norm_nonneg _))
    _ = (∑q:L,‖w q‖)*W:=(sum_mul ..).symm
    _ ≤ _:=mul_le_mul_of_nonneg_right cash nonneg

end YM.Integration.WilsonIndependentConditionedDenseFilmLast
end
