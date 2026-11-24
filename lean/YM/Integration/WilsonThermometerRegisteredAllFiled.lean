import YM.Integration.WilsonThermometerRegisteredTrace
import YM.Integration.WilsonThermometerNumericalStation
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredAllFiled

open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Ac OPE.Therm WilsonLimitConstruction RG16 MSbar.Heath Labels Source Pert.Asymptotics
open WilsonRootedKioskOccupiedSlip WilsonRegisteredAffineHalo WilsonRegisteredAxialRates
open WilsonReportingForestAngularFare WilsonJointAxialRoster
open Multi Extra.Trajectories Comparison.RG02.Cumulants WilsonIndependentOrdinaryPairGrade
open FVA1 Cells Extraction Table Climb Trace Trace.Pilot
open WilsonPositionThermometerCapStation WilsonOriginalThermometerPalette WilsonOriginalThermometerMicroscopic
open WilsonThermometerCourseHearing WilsonThermometerRegisteredPair WilsonPositionThermometerGradedReading
open WilsonPositionThermometerGradedSource
open scoped Classical BigOperators Topology

open WilsonOriginalReceivedChain FVA1Physical.TwoReset QuadraticLocal.Rebirth
local notation "names₀" => WilsonThermometerCourseHearing.disks
local notation "sectors₀" => WilsonThermometerCourseHearing.sectors
local notation "J₀" => Stock.census (Fin 3)

variable {G:Gauge} (R:Run G) (A:Group R.family 6) {m i per k:ℕ}
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (school:Syl.School k)
  (o:Positions (Fin 3) (R.family.side (i+2) per))

local notation "first" => Nat.lt_succ_self (i+1)
local notation "tape" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "gf" => Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
def numerical (x:Wallet names₀) (z:Stationary.Link G (R.family.side i per)) : Poly (J₀) :=
  let bare:=WilsonThermometerNumericalStation.numerical R A π school o x
  let program:=WilsonOriginalCoveredEvolution.run R first π Γ (Burn.horizon k+2) school.order levels bare
  Poly.pass (WilsonCoherentMayerWindingGrades.panel school.order (gf:ℂ)
    (fun d=>program i (Nat.le_succ i) _ (dvd_refl _) d z))

variable (simple:G.Simple) (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (Ψ:∀ j,RG.Rep G (R.family.side j per)) {φ:ℕ→ℕ}
  (books:Mentor.Offices.Books D R.rolls Q φ) (ahead:Mentor.Forecast D R.rolls Q φ books)
  (floor:m ≤ i)
local notation "hi" => floor.trans (Nat.le_succ i)
local notation "head" => WilsonThermometerCourseHearing.offered R A simple first o
local notation "carrier" n:max floor₁:max source:max =>
  Post (N:=i+2) R hk D Q π Γ Ψ books ahead names₀ sectors₀ levels school.order school.horizon school.pieces
    n floor₁ source
local notation "pupil" j:max pro:max Z:max => Oak.student (n:=per) (i:=j) R hk D Q π Γ books pro
  (Z).op (Z).lesson ahead names₀ (Z).model school.order (Z).voter
local notation "start" x:max => WilsonThermometerRegisteredPupil.bare R A D π (φ:=φ) school o x

theorem on_trail (top:carrier (i+1) (hi) (head))
    {Y:Wallet names₀ → Config G (R.family.side (i+1) per) → Poly (J₀)}
    (P:carrier i floor Y) (course:Concourse R.alloy R.kit R.T π Γ m (i+2) per k Ψ)
    (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (fits:school.order ≤ Burn.horizon k+1) (shelf:school.horizon ≤ R.alloy.B.a.clock.J m)
    (entry:∀ x:Wallet names₀, ∀ (grid:Side) (div:(R.family.side (i+1) per).val∣grid.val) (d:ℕ),
      d ≤ school.order → ∀ z,(start x) grid div d z=peek div (pupil (i+1) (hi) top)
        levels (π (i+2)) tape x d z)
    (trail:WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead names₀ sectors₀ levels school.order school.horizon
      school.pieces (hi) (head) top i floor Y P) (x:Wallet names₀) (z:Stationary.Link G (R.family.side i per)) :
    let teacher:=pupil i floor P
    let writer:=Air.craft teacher (fun v=>(teacher v).paint x) levels (π i) tape
    let angle:=Stationary.arm G (R.family.side i per) 1 z
    numerical R A π Γ school o x z=Poly.pass
      (WilsonCoherentMayerWindingGrades.panel school.order (gf:ℂ) (fun d=>Air.discharge writer d angle)) := by
  intro teacher writer angle
  obtain ⟨ib,filed⟩:=WilsonOriginalCoveredHearing.evaluated R hk D Q π Γ Ψ books ahead names₀ sectors₀
    levels school.order school.horizon school.pieces (hi) (head) top x (start x) first course pass month
    fits shelf (entry x) trail
  simp only [numerical,←WilsonThermometerNumericalStation.returned R A D π Γ (φ:=φ) school o x]
  exact congrArg Poly.pass (filed (gf:ℂ) z)

end YM.Integration.WilsonThermometerRegisteredAllFiled
