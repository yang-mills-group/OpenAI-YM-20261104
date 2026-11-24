import YM.Integration.WilsonReceivedChronologicalRosterInteriorCourse
import YM.Integration.WilsonReceivedChronologicalRosterFork
import YM.Integration.WilsonReceivedChronologicalRosterCourse

/-! The one occupied finite source is elected before every cutoff and arbitrary independent programme. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterInteriorPortal
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Embroider WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar WilsonOriginalAllOrderCourse
open WilsonOriginalOpticalSchedule WilsonIndependentCollarCensusCourse WilsonOriginalCollarElection
open WilsonReceivedFixedDigitHistory WilsonReceivedCanonicalVerseBasis WilsonThermometerDeclaredSeeds
open FundedMarkedPathSelection WilsonIndependentCollarAddressedSource Comparison.Density.Transport Pert.Asymptotics
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV QuadraticLocal QuadraticLocal.Mentor
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge}{a:Axis}{simple:G.Simple}{ε:ℝ}{s:WilsonOriginalAllOrderCourse.Schedule G}
  {R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}{U:Type}[Fintype U]


open Marker Multi QuadraticLocal QuadraticLocal.Earn

open WilsonOriginalCensusDatedSchools (Paired)
open WilsonOriginalCensusMeasuredStation (CreditAt)
open WilsonCoeffUV.Bank.Carp

open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusFundedAttendance
open WilsonOriginalCensusAttendanceStation WilsonOriginalCensusPublicationClock

open Function Filter Finset Lattice RG RG.Supply Org PhysicalNext.Repeat Legato
open Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open AllOrder AllOrder.Floe QuadraticLocal QuadraticLocal.Rebirth QuadraticLocal.Sunrise.Aviary
open AllOrder.Transit AllOrder.Transit.WheelP
open WilsonOlderFreshGraphAward WilsonThermometerDeclaredSeeds
open WilsonOriginalMeasuredOccupiedForest (Read)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetDepositedGeometric WilsonOriginalOccupiedForestIntegral
open WilsonMarkedKineticDefect WilsonMarkedKineticGerm
open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusAttendanceStation
open WilsonMarkedIndependentPhysicalIntake
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi
open WilsonVacuumPreResetTorusDeposit (bank)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (MassCall)
open AllOrder.Floe.Step
open AllOrder.Ker Primitives.TwoWave.RealSlice
open WilsonVacuumPreResetDatedDeposit (Issued)
open FVA1Physical.TwoReset (AffineMass)
open PertExtension.Series PowerSeries
open AllOrder AllOrder.Floe
open AllOrder.Floe.Step.PlanV FVA1Physical.TwoReset
open WilsonVacuumPreResetDatedCourse (coin)
open Primitives.TwoWave.RealSlice
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonOriginalOccupiedForestIntegral (numerator)
open Next.SectorChange MeasureTheory

open WilsonOriginalCensusFiledAttendance (QuietAt)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedCanonicalVerseBasis OriginalMarkedSourceComet
open Multi WilsonCoeffUV.Blue


open WilsonReceivedChronologicalFixedReserve (terms charges)
open WilsonReceivedChronologicalFixedEarner (programme start)
open WilsonReceivedChronologicalFixedEnrollment (Cohort)
open WilsonReceivedChronologicalFixedTariff (gross allowance)
open WilsonOriginalCensusFaceAdmission (housed)
open WilsonReceivedChronologicalMaterialLine (homes)
open WilsonReceivedChronologicalMaterialApertures (spread diameter)
open WilsonOriginalCensusDatedPeriodOpening (Opened)
open WilsonOriginalCensusDatedHeldTariff (Rates)
open WilsonOriginalFixedTestCensusPublicBase (base)
open WilsonOriginalCensusPublicationClock (Open)


open WilsonCenteredPhysicalPanel
open StressFlux.Matching Next.UVStress
open WilsonReceivedChronologicalFixedPlaced (Purchased)
open WilsonReceivedChronologicalFixedPorts (Period)

open WilsonReceivedCanonicalSocketSeed (contact)
open WilsonAddressedPublicSubmittedDates (grades positive)
open WilsonAddressedPublicFirstPeriod (appointment)
open WilsonAddressedPublicFirstRoseCampus (seller financed)
open WilsonOriginalReflectedFirstPanels (Sold)

open WilsonMovingForkStencilCatalogue (Catalogue)

def Campus (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)
    {arity:ℕ}(head:Fin arity)(subjects:Fin arity → ℕ)(adult:∀i,0<subjects i)(D:Fin arity → ℕ)(pt:Fin arity → Chamber)
    (caps:Fin arity → ℝ)
    (rent:∀i,‖WilsonReceivedCanonicalSocketSeed.present D i‖≤caps i)(φ:Test arity)(requested A:ℕ)(tol η:ℝ)(tp:0 < tol)(ep:0 < η)(school:ℕ)(tube:LinkTube G)
    (pieces physical:ℕ)(p:Bool → ℕ)(span:U → ℕ)(lag:U → Bool → ℕ):Prop:=
    let n:=arity
    let _front:Fin n:=head
    let k:=subjects
    let κ:∀v:Fin arity,Knob (D v):=fun v=>contact (D v)
    let power:=fun _:Fin arity=>0
    let target:=WilsonOriginalReflectedFirstTerms.order R k requested
    let P:=target+1
    let menu:=terms k power P
    let ask:=programme k power P
    let L:=R.family.path.levels
    let _firstPeriod:=appointment R simple k D pt (fun _=>4) tube ask.order ask.order menu.target menu.precision
      (seller G) (financed paid) (WilsonAddressedPublicFirstRanks.original k P).2.2.2.1
    ∃book:WilsonOriginalCensusPhysicalAttendance.Room (prepared s) R simple,
    ∃price:Credit,∃B:ℝ,1 ≤ B ∧ ∀ᶠ o:ℕ in atTop,
    WilsonSingleHardRadius.first R simple ≤ o ∧
    WilsonOriginalCensusCanonicalAppointedClock.opening R simple (seller G) (financed paid) paths
      (Burn.horizon ask.vac) ≤ o ∧
    ∃resident:(N:ℕ) → o ≤ N → Day (prepared s) R simple ask.school o N,
    (∀N:ℕ,∀live:o ≤ N,∃Z:ℕ → SeriesA G,QuietAt (resident N live) price Z) ∧
    ∀ᶠ anchor:ℕ in atTop,∃V:Realm G (menu.order+1) Credit.leanC,∃draw:V.draws=L,
      V.paid=R.metals.O ∧ V.anchor=anchor ∧ ∀ᶠ m:ℕ in atTop,
      ∃old:o ≤ m, ∀j:ℕ, ∀mj:m+1 ≤ j,
      L.S.scale (j+1+1)-L.S.scale m≤(A:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))) →
      ∀f:ℕ, ∀fine:f ≤ j+1+1,∃source:Catalogue R k (j+1+1),∀ᶠ per:ℕ in atTop,
        ∀N:ℕ,∀valid:j+1+1 ≤ N,
        WilsonReceivedChronologicalRosterFork.Hired paid head subjects adult D pt caps φ requested A tol η tp ep
          school tube pieces physical p span lag book B o resident V draw m j old mj f fine rent source per N valid ∧
        ∀pupil:WilsonReceivedChronologicalFixedPlaced.Purchased
            (per:=per) (V:=V) (draw:=draw) (rate:=(Real.sqrt (R.family.path.β N per (m+1)))^(1:ℝ)*B^n)
            (allowance:=1) power P book (resident N (by omega)) κ pt (j+1+1) m valid
            (fun l=>base B caps power (L.clock.hatBeta (l+1))) old φ caps A target η,
          WilsonReceivedChronologicalRosterInterior.Paid
            (per:=per) (V:=V) (draw:=draw) (rate:=(Real.sqrt (R.family.path.β N per (m+1)))^(1:ℝ)*B^n)
            (allowance:=1) power P book (resident N (by omega)) κ pt (j+1+1) m valid
            (fun l=>base B caps power (L.clock.hatBeta (l+1))) old caps A target η pupil


theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)
    {arity:ℕ}(head:Fin arity)(subjects:Fin arity → ℕ)(adult:∀i,0<subjects i)(D:Fin arity → ℕ)(pt:Fin arity → Chamber)
    (caps:Fin arity → ℝ)(nonneg:∀v,0 ≤ caps v)(hk:∀v,subjects v < D v)
    (rent:∀i,‖WilsonReceivedCanonicalSocketSeed.present D i‖≤caps i)(φ:Test arity)(requested A:ℕ)(tol η:ℝ)(tp:0 < tol)(ep:0 < η)(school:ℕ)(tube:LinkTube G)
    (pieces physical:ℕ)(p:Bool → ℕ)(span:U → ℕ)(lag:U → Bool → ℕ):
    Campus paid paths head subjects adult D pt caps rent φ requested A tol η tp ep school tube pieces physical p span lag :=by
  classical
  unfold Campus
  intro n front k κ power target P menu ask L clock0
  obtain ⟨book,price,B,one,cohort⟩:=WilsonReceivedChronologicalRosterInteriorCourse.original paid paths n head subjects adult D pt caps
    nonneg hk φ requested A tol η tp ep school tube pieces physical p span lag
  refine ⟨book,price,B,one,?_⟩
  filter_upwards [cohort] with o entry
  obtain ⟨hard,activated,resident,quiet,enrolled⟩:=entry
  refine ⟨hard,activated,resident,quiet,?_⟩
  filter_upwards [enrolled] with anchor entered
  obtain ⟨V,draw,metal,based,wages⟩:=entered
  refine ⟨V,draw,metal,based,?_⟩
  filter_upwards [wages 1 (by norm_num) le_rfl] with m dates
  obtain ⟨old,grades⟩:=dates
  refine ⟨old,?_⟩
  intro j mj window f fine
  obtain ⟨source,accepted⟩:=WilsonReceivedChronologicalRosterFork.original
    paid paths head subjects adult D pt caps φ requested A tol η tp ep school tube pieces physical p span lag
    book B o resident V draw m j old mj f fine rent hard activated
  refine ⟨source,?_⟩
  have align:m+(j+1+1-m)=j+1+1:=by omega
  have eligible:L.S.scale (m+(j+1+1-m))-L.S.scale m≤(A:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))):=by
    simpa only [align] using window
  have issued:=grades (j+1+1-m) (by omega) eligible
  simp only [align] at issued
  filter_upwards [issued] with per funded
  intro N valid
  obtain ⟨pupil,interior,firstAt,venue,sparse,period,current,geo,ranked,stages,atj,go,board⟩:=funded N valid
  refine ⟨accepted per N valid ?_,interior⟩
  refine ⟨pupil,?_,?_,firstAt,venue,sparse,period,current,geo,ranked,stages,atj,go,board⟩
  · exact WilsonOriginalReflectedFirstPanels.original (R:=R) (simple:=simple) (d:=k) (P:=P)
      (school:=book) (day:=(resident N (by omega))) (old:=old) (early:=by omega) (live:=valid) (lens:=D) (pt:=pt)
      (toll:=fun l=>base B caps power (L.clock.hatBeta (l+1))) (classroom:=pupil)
      (nonempty:=(Nat.zero_lt_of_lt head.isLt)) (adult:=adult) (seller:=seller G) (fund:=financed paid) (history:=paths)
      (tube:=tube) (ep:=ep) (tp:=tp) (authorized:=stages) (activated:=activated) (ranked:=ranked)
      (faculty:=atj) (venue:=venue.trans (by omega)) (go:=go) (board:=board) (floorOld:=hard)
      (geo:=geo) (support:=paid.support)
  · exact WilsonIndependentConditionedLocatedFirstPanels.original (R:=R) (simple:=simple) (d:=k) (P:=P)
      (school:=book) (day:=(resident N (by omega))) (old:=old) (early:=by omega) (live:=valid) (lens:=D) (pt:=pt)
      (toll:=fun l=>base B caps power (L.clock.hatBeta (l+1))) (classroom:=pupil)
      (nonempty:=(Nat.zero_lt_of_lt head.isLt)) (adult:=adult) (seller:=seller G) (fund:=financed paid) (history:=paths)
      (tube:=tube) (ep:=ep) (tp:=tp) (authorized:=stages) (activated:=activated) (ranked:=ranked)
      (faculty:=atj) (venue:=venue.trans (by omega)) (go:=go) (board:=board) (floorOld:=hard)
      (geo:=geo) (support:=paid.support)

end YM.Integration.WilsonReceivedChronologicalRosterInteriorPortal
end
