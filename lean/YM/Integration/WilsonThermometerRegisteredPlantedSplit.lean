import YM.Integration.WilsonThermometerRegisteredPlantedFaces
import YM.Integration.WilsonMeasuredScalarRegular

/-! On the nominated Wilson vacuum the full signed scalar splits into its localized
numerical program, the paid scalar regular correction, and the marked hard numerator
on its genuine quiet partners. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredPlantedSplit

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


open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection
local notation "physical₁" Q₀:max => WilsonThermometerRegisteredPlantedFaces.physical R A o Q₀
local notation "numerical₁" Q₀:max => WilsonThermometerRegisteredPlantedFaces.predicted R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀
local notation "declared₁" Q₀:max => WilsonThermometerRegisteredOlderMaterial.declared R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀ fired
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "rep₁" => R.family.path.rep (i+2) per i

def retained (Q₀:Poly (faces)) (h:Coefficient (frame) (R.family.side i per))
    (U:Config G (R.family.side i per)) : ℂ :=
  (physical₁ Q₀) U - (numerical₁ Q₀) U - (dose U)⁻¹*account h (Ψ i) U

include course in
theorem corrected (ref:∀v,R.family.ref ((ids) v) ≤ i+2) (Q₀:Poly (faces))
    (h:Coefficient (frame) (R.family.side i per)) (y:Site (R.family.side i per)) {M:ℝ}
    (fmt:h.Format y R.family.params (Ψ i)) (paid:h.remBound y (Ψ i) κ M)
    (density:∀ U,h.density y (section₀) (Ψ i) U=(total (original U) Q₀).part full-
      (dose U)*(total (Poly.pass (bare lamps fired U)) Q₀).part full) :
    let regular:=h.exponentialEntry y (section₀) (rep₁)
    (retained R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀ h=fun U=>
      (declared₁ Q₀) U+regular U) ∧ Measurable regular ∧ (∀U,‖regular U‖ ≤ ‖h.x 0‖+M) ∧
    ∀U,account h (Ψ i) U≠0→∃ l,h.forced l U≠0 ∧ y∈((rep₁).activities.forced l).support ∧
      ∃ z,z∈((rep₁).activities.forced l).inventory ∧ z∈flags (rep₁).p.threshold U := by
  intro regular
  obtain ⟨shape,owners,-⟩:=WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course hi (cut).le
  have law:(Ψ i).eval=(rep₁).eval:=(course.1.walk i hi (cut).le).view
  obtain ⟨f,r,value,witness⟩:=WilsonMeasuredOnlyHard.original h (rep₁) (Ψ i) shape law owners
    (section₀) R.family.params y κ M fmt paid
  have read (U):h.density y (section₀) (Ψ i) U=(dose U)*regular U+account h (Ψ i) U:=by
    rw [value U,WilsonPhysicalMarkedDefect.RegularProjection.density h y (rep₁) (section₀),law]
  have eq:=WilsonThermometerRegisteredPlantedFaces.same R simple A hk D Q π Γ Ψ course books hi ahead school o P
    hearing J axes ref Q₀ h y density
  have nz (U):((rep₁).eval U:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (RG02.Actual.eval_pos R.makes.wilson (cut).le U).ne'
  refine ⟨?_,?_,?_,witness⟩
  · funext U
    have orig:=congrFun eq U
    dsimp only [WilsonThermometerRegisteredPlantedFaces.observed] at orig
    rw [read U,law,mul_add,←mul_assoc,inv_mul_cancel₀ (nz U),one_mul] at orig
    unfold retained;rw [law]
    linear_combination orig
  · have good := (R.makes.wilson.represents (i+2) per i (cut).le).good
    have num := (Coefficient.envelope (section₀) good r f).meas
    have den := Complex.continuous_ofReal.measurable.comp ((rep₁).envelope good).meas
    have cell:regular=fun U=>(soft h).density y (section₀) (rep₁) U/((rep₁).eval U:ℂ):=by
      funext U;rw [WilsonPhysicalMarkedDefect.RegularProjection.density h y (rep₁) (section₀),
        mul_div_cancel_left₀ _ (nz U)]
    rw [cell];exact num.div den
  · exact WilsonMeasuredScalarRegular.point R simple (rep₁) (soft h) y r

include course in
theorem earlier (ref:∀v,R.family.ref ((ids) v) ≤ i+2) (Q₀:Poly (faces))
    (h:Coefficient (frame) (R.family.side i per)) (y:Site (R.family.side i per)) {M B K:ℝ}
    (fmt:h.Format y R.family.params (Ψ i)) (paid:h.remBound y (Ψ i) κ M)
    (density:∀ U,h.density y (section₀) (Ψ i) U=(total (original U) Q₀).part full-
      (dose U)*(total (Poly.pass (bare lamps fired U)) Q₀).part full)
    (size:(frame).coeffSize h.x ≤ K) (root:RG.Envelope (declared₁ Q₀))
    (price:(∫ U,‖(declared₁ Q₀) U‖ ∂scene R.family.path (i+2) per i)≤B) :
    let X:=retained R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀ h
    RG.Envelope X ∧ ∀ j(age:j ≤ i),
      (∫ U,‖actualTransport R.family (N:=i+2) X age U‖ ∂scene R.family.path (i+2) per j)≤B+(K+M) := by
  intro X
  obtain ⟨eq,borel,point,_⟩:=corrected R simple A hk D Q π Γ Ψ course books hi ahead school o P hearing J axes
    ref Q₀ h y fmt paid density
  have unit:‖h.x 0‖≤K:=le_trans (Finset.single_le_sum (f:=fun l=>‖h.x l‖) (fun _ _=>norm_nonneg _) (Finset.mem_univ 0)) size
  have good (U):‖h.exponentialEntry y (section₀) (rep₁) U‖≤K+M :=
    (point U).trans (add_le_add unit (le_refl M))
  change RG.Envelope (retained R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes Q₀ h) ∧ _
  change RG.Envelope X ∧ _
  have joined : X=fun U=>(declared₁ Q₀) U+h.exponentialEntry y (section₀) (rep₁) U:=eq
  rw [joined]
  refine ⟨?_,?_⟩
  · obtain ⟨mb,C,hC⟩:=root
    exact ⟨mb.add borel,C+(K+M),fun U=>(norm_add_le ..).trans (add_le_add (hC U) (good U))⟩
  · exact fun j age=>WilsonThermometerRegisteredOlderMaterial.combined R (cut).le age _ _ root borel B (K+M) price good

end YM.Integration.WilsonThermometerRegisteredPlantedSplit
