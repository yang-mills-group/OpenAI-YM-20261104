import YM.Integration.WilsonThermometerRegisteredOlderMaterial
import YM.Integration.WilsonThermometerFullSignedPower
import YM.Integration.WilsonThermometerCourseResidual

/-! On the nominated finite Wilson course, subtract its actual one-source density
from the planted three-field observation. This leaves exactly the returned full ordinary
program, including the quiet term of the inverse and all six proper faces. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredPlantedFaces

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

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m i per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m (i+2) per k Ψ)
  {φ:ℕ → ℕ} (books:Mentor.Offices.Books D R.rolls Q φ) (hi:m ≤ i)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (school:Syl.School k) (o:Positions (Fin 3) (R.family.side (i+2) per))
local notation "cut" => (Nat.lt_succ_of_lt (Nat.lt_succ_self i))
local notation "faces" => Stock.census (Fin 3)
local notation "source₀" => WilsonThermometerCourseHearing.offered R A simple cut o
variable (P:WilsonOriginalReceivedChain.Post (N:=i+2) R hk D Q π Γ Ψ books ahead WilsonThermometerCourseHearing.disks sectors levels
  school.order school.horizon school.pieces i hi (WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_of_lt (Nat.lt_succ_self i)) o))

local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead WilsonThermometerCourseHearing.disks
  P.model school.order P.voter
local notation "lamps" => (rendered student (Ψ i).p (Coat.gStep (Ψ (i+1)).beta))
local notation "placed" => P.passport.coarser (R.family.path.levels.clock.op i per).ratio
local notation "n" => (school.order+school.horizon+2)
local notation "gf" => Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
local notation "stage" => R.alloy.B.a.clock.J i


open MeasureTheory
open private exponential from YM.Integration.WilsonFiniteProgramFieldBorel
local notation "tape" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "names₀" => WilsonThermometerCourseHearing.disks
variable (hearing:ℕ) (J:Voice G) (axes:Lattice.Order)
local notation "H₁" => radius R (invoice (Fintype.card (Fin 3)) (hearing+2*n)) 1 i
local notation "r₁" => amplitude R J (H₁) (i+2) per i
local notation "h₁" => (WilsonDegreeFourInheritedRange.height R (hearing+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1
local notation "τ₁" => angularCut (R.family.path.levels.clock.hatBeta i)
local notation "cold" => House.chilly (G:=G) (plaquettes (placed).origin (H₁)) (τ₁)
local notation "angle₁" => WilsonJointAxialHearing.angleOf (placed).origin (h₁) J axes (r₁) gf
local notation "link₁" z:max =>
  WilsonCapturedPrimaryPotential.potential gf ((r₁) • WilsonJointAxialWindow.direction (placed).origin (h₁) J axes (r₁) z)
local notation "who" x:max =>
  Air.craft student (fun v=>(student v).paint x) levels (π i) tape
local notation "intake" x:max => Air.craft P.model (fun v=>(P.model v).paint x) levels (π (i+1)) tape
local notation "step₁" => (RunFormalChain.fromRun R).step (i+2) i per cut
local notation "bank" x:max z:max => WilsonThermometerRegisteredAllFiled.numerical R A π Γ school o x z
local notation "panel₀" x:max z:max =>
  WilsonCoherentMayerWindingGrades.panel school.order (gf:ℂ) (fun d=>Air.discharge (who x) d z)


open WilsonThermometerCenteredAlgebra WilsonFiniteOrdinaryInverse Primitives.GCC.Anchor WilsonReceivedWholeFieldHot
open Multi Extra.Trajectories Comparison.RG02.Cumulants WilsonIndependentOrdinaryPairGrade Push.AbsoluteSums

local notation "finite₁" x:max F:max t:max U:max =>
  Order.value (gf:ℂ) (Order.ratio (Bulk.Fk (step₁) F t (intake x) (angle₁ U) school.order))


open FVA1 Planned.GuardedAtom Push.Local Extra.Histories Next.Foundations RG16.Literal Next.Rank Next.UVStress
open MergeProof.East OriginalForcedAddresses Exterior WilsonThermometerCourseIntake WilsonThermometerWeightedCapture
local notation "frame" => R.family.labels.level 0
local notation "section₀" => R.family.localSection 0
local notation "dose" U:max => ((Ψ i).eval U : ℂ)
local notation "original" U:max => (incoming R A simple (cut).le o U)
local notation "ids" => (fun h:Fin 3=>WilsonPositionThermometerCapStation.index A
    (WilsonPositionThermometerGradedSource.grade h))
local notation "vector₀" => WilsonPositionThermometerGradedReading.vector A (Finset.univ:Finset (Fin 3))

def physical (Q₀:Poly (faces)) (U:Config G (R.family.side i per)) : ℂ :=
  ∑s:(faces).Mode,weight Q₀ s*actualTransport R.family (N:=i+2)
    (fun V=>∏ h∈s.val,R.family.O (i+2) per
      (A.station.wheel.atCut (i+2,per) ((ids) h) ((vector₀) h)) (o.origin h) V) (cut).le U

def predicted (Q₀:Poly (faces)) (U:Config G (R.family.side i per)) : ℂ :=
  (cold).indicator (fun V=>(total (bank fired (link₁ V)) Q₀).part full) U

def observed (Q₀:Poly (faces)) (h:Coefficient (frame) (R.family.side i per)) (y:Site (R.family.side i per))
    (U:Config G (R.family.side i per)) : ℂ :=
  physical R A o Q₀ U - predicted R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀ U -
    (dose U)⁻¹*h.density y (section₀) (Ψ i) U

include course hi in
theorem planted (ref:∀v,R.family.ref ((ids) v) ≤ i+2) (Q₀:Poly (faces))
    (U:Config G (R.family.side i per)) :
    physical R A o Q₀ U = (dose U)⁻¹*(total (original U) Q₀).part full := by
  rw [physical,affine,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have field:=WilsonThermometerCourseResidual.observed R A simple (cut).le o ref U s
  change ((R.family.path.rep (i+2) per i).eval U:ℂ)⁻¹*(original U).part s = _ at field
  have law:(Ψ i).eval=(R.family.path.rep (i+2) per i).eval := (course.1.walk i hi (cut).le).view
  rw [←field,law]; ring

theorem filed (Q₀:Poly (faces)) (U:Config G (R.family.side i per)) :
    WilsonThermometerRegisteredOlderMaterial.declared R simple A hk D Q π Γ Ψ books hi ahead school o P
      hearing J axes Q₀ fired U=(total (Poly.pass (bare lamps fired U)) Q₀).part full-
        predicted R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀ U := by
  unfold WilsonThermometerRegisteredOlderMaterial.declared predicted
  by_cases hU:U∈cold
  · simp only [Set.indicator_of_mem hU,affine,mul_sub,Finset.sum_sub_distrib]
  · simp only [Set.indicator_of_notMem hU,affine,sub_zero]

include course hi in
theorem same (ref:∀v,R.family.ref ((ids) v) ≤ i+2) (Q₀:Poly (faces))
    (h:Coefficient (frame) (R.family.side i per)) (y:Site (R.family.side i per))
    (density:∀ U,h.density y (section₀) (Ψ i) U=(total (original U) Q₀).part full-
      (dose U)*(total (Poly.pass (bare lamps fired U)) Q₀).part full) :
    observed R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀ h y =
      WilsonThermometerRegisteredOlderMaterial.declared R simple A hk D Q π Γ Ψ books hi ahead school o P
        hearing J axes Q₀ fired := by
  funext U
  rw [observed,planted R simple A π Γ Ψ course hi o ref Q₀ U,
    filed R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀ U,density U]
  have law:(Ψ i).eval=(R.family.path.rep (i+2) per i).eval := (course.1.walk i hi (cut).le).view
  have positive:(dose U)≠0:=by
    rw [law]
    exact Complex.ofReal_ne_zero.mpr (RG02.Actual.eval_pos R.makes.wilson (cut).le U).ne'
  field_simp [positive]
  ring

end YM.Integration.WilsonThermometerRegisteredPlantedFaces
