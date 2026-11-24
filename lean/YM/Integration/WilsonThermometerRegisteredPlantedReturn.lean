import YM.Integration.WilsonThermometerRegisteredPlantedSplit
import YM.Integration.WilsonThermometerFullSignedAppointment

/-! The compensated original Wilson source on the coissued two-date post,
at arbitrary purchased order, heard through the same filed finite history.
The only term retained separately is its own normalized marked hard numerator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredPlantedReturn

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

local notation "C₃" => WilsonFiniteOrdinaryInverse.fee (faces)
local notation "profit" p:max => WilsonReceivedCloseOrdinaryGrade.invoice (faces) 3 0 (p+160) 1
local notation "extras" p:max => (4:ℝ)^(p+161+2*n*3)*(Fintype.card (Multi.parts (faces)).Mode)*((2:ℝ)^n)^3
variable (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
  Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)


open WilsonThermometerFullSignedPower WilsonMeasuredCoefficientTransport
local notation "coeffRent" α:max => WilsonFullFaceSignedPower.constants (section₀) R.family.params α ((2:ℝ)^n+4)
local notation "oldCost" p:max => C₃*((profit p)+(extras p))*gf^(p+1)+C₃*(profit p)*gf^(p+1)
local notation "hitCost" p:max α:max => |C₃*(coeffRent α)| *(4^hearing+2)*gf^(p+1)
local notation "unitCost" p:max => |testPrice (frame)*C₃*WilsonFullFaceSignedPower.inter*
    (Fintype.card (Multi.parts (faces)).Mode:ℝ)*125| *gf^(p+1)
local notation "actual₁" Q₀:max h:max => WilsonThermometerRegisteredPlantedSplit.retained R simple A hk D Q π Γ Ψ
    books hi ahead school o P hearing J axes Q₀ h

def Report (p:ℕ) (Q₀:Poly (faces)) (y:Site (R.family.side i per)) (α:ℝ) : Prop :=
  ∃ h:Coefficient (frame) (R.family.side i per), h.Format y R.family.params (Ψ i) ∧
    h.remBound y (Ψ i) κ (hitCost p α) ∧ (frame).coeffSize h.x ≤ unitCost p ∧
    (∀U,h.density y (section₀) (Ψ i) U=(total (original U) Q₀).part full-
      (dose U)*(total (Poly.pass (bare lamps fired U)) Q₀).part full) ∧
    (∀U,account h (Ψ i) U≠0→∃ l,h.forced l U≠0 ∧ y∈((rep₁).activities.forced l).support ∧
      ∃ z,z∈((rep₁).activities.forced l).inventory ∧ z∈flags (rep₁).p.threshold U) ∧
    RG.Envelope (actual₁ Q₀ h) ∧ ∀ j(age:j ≤ i),
    (∫ U,‖actualTransport R.family (N:=i+2) (actual₁ Q₀ h) age U‖ ∂scene R.family.path (i+2) per j)
       ≤ (oldCost p)+((unitCost p)+(hitCost p α))

include course in
theorem on_post {η:ℝ} {T:Campaign R} {W:Campaign.Pillars R T}
    (funded:FundedOriginalProperties.{u} simple η W)
    (slow:WilsonWindowReportingPace.Slow R.kit)
    (clear:Clear G J) {ε:ℝ} (ep:0<ε) (modest:ε ≤ (1:ℝ)/4) (p:ℕ)
    (reserve:(p+1)+247 ≤ hearing)
    (law:VowsR.LawScroll G φ) (enrolled:VowsR.Chamber law R.kit D Q books)
    (fund:Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (late:max (WilsonJointAxialRoster.opening R simple funded slow.2 J clear (Fintype.card (Fin 3)) n hearing ep)
        (WilsonReceivedAxialFiling.opening R simple D φ width school.order school.horizon (Fintype.card (Fin 3)) ep) ≤ i)
    (finiteLate:max (WilsonReceivedAxialFinite.opening R simple hearing ep)
        (WilsonReceivedAxialFinite.massOpening R D levels school.order school.horizon school.pieces (k:=k) simple width) ≤ i)
    (clockLate:(eventually_atTop.mp (WilsonJointAxialClock.original R simple)).choose ≤ i)
    (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fit:k ≤ stage) (visible:WilsonThermometerRegisteredAllStation.Visible R simple A hk D Q π Γ Ψ books
      school o ahead hi P hearing ε)
    (Q₀:Poly (faces)) (price:Poly.price (fun v=>gf*P.w v) (inverseMass Q₀) ≤ C₃)
    (fraction:ε*(3^hearing+2) ≤ 1) (gate:WilsonReportingForestAngularReflection.posted R)
    (rareLate:WilsonJointAxialScalar.opening (V:=Fin 3) R simple gate hearing n (p+161+2*n*3) ≤ i)
    (F:Forest (R.family.path.levels.clock.op i per).ratio) (tag:(R.family.path.levels.clock.op i per).Choices)
    (way:WayStation R.kit) (station:WilsonCenteredCaptureClock.first R simple ≤ i) (sec:R.t 0 ≤ i)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (early:(eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow.2 ready)).choose ≤ i)
    (haloPay:(eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (force:hearing ≤ stage) (deep:2*(hearing+1)+8 ≤ school.order) (aged:hearing+4≤3*k+2)
    (opened:WilsonThermometerFullSignedAppointment.gate R simple school hearing deep aged ≤ i)
    (saved:(eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple hearing)).choose ≤ i)
    (ref:∀v,R.family.ref ((ids) v) ≤ i+2)
    (y:Site (R.family.side i per)) (Z:Support (R.family.side i per)) (center:y∈Z)
    (taken:∀v:Fin 3,(placed).origin v∈Z) (rad:ℕ) (near:∀v:Fin 3,separation ((placed).origin v) y ≤ rad)
    (radius:rad ≤ (Ψ i).p.B) (box:Z⊆halo (Ψ i).p.B {y}) (α:ℝ) (strength:(Ψ i).p.supportExponent ≤ α) :
    Report R simple A hk D Q π Γ Ψ books hi ahead school o P hearing J axes p Q₀ y α :=by
  have booked:=WilsonThermometerFullSignedAppointment.on_post R simple A hk D Q π Γ Ψ course books school o ahead hospital
    slow hi P way station sec ready early haloPay pass hearing (p+1) reserve force deep aged opened saved modest visible
  obtain ⟨h,fmt,rent,field,size⟩:=booked Q₀ y Z center taken rad near radius box α strength price
  have prior:=WilsonThermometerRegisteredOlderMaterial.on_post R simple A hk D Q π Γ Ψ course books hi ahead school o P
    hearing J axes width funded slow.2 clear ep (le_trans modest (by norm_num)) p (by omega) (by omega)
    law enrolled fund late finiteLate clockLate pass hospital fit visible Q₀ price fraction gate rareLate fired F tag
  have billed:=prior.2 i (le_refl i)
  simp only [actualTransport_base R.family R.makes (cut).le] at billed
  obtain ⟨env,heard⟩:=WilsonThermometerRegisteredPlantedSplit.earlier R simple A hk D Q π Γ Ψ course books hi ahead school
    o P hearing J axes ref Q₀ h y fmt rent field size prior.1 billed
  have own:=WilsonThermometerRegisteredPlantedSplit.corrected R simple A hk D Q π Γ Ψ course books hi ahead school
    o P hearing J axes ref Q₀ h y fmt rent field
  exact ⟨h,fmt,rent,size,field,own.2.2.2,env,heard⟩

end YM.Integration.WilsonThermometerRegisteredPlantedReturn
