import YM.Integration.WilsonReceivedChronologicalRosterFunded
import YM.Integration.WilsonReceivedChronologicalRosterSettled
/-! One fixed finite cohort, its actual two stopped readings, and their complete restored financial opening. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterCertified
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

def Admitted (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)
    {arity:ℕ}(head:Fin arity)(subjects:Fin arity → ℕ)(adult:∀i,0<subjects i)(D:Fin arity → ℕ)(pt:Fin arity → Chamber)
    (caps:Fin arity → ℝ)
    (rent:∀i,‖WilsonReceivedCanonicalSocketSeed.present D i‖≤caps i)(φ:Test arity)(reserve window wanted pole A travel:ℕ)(budget α:ℝ)(tol η:ℝ)(tp:0 < tol)(ep:0 < η)(school:ℕ)(tube:LinkTube G)
    (pieces physical:ℕ)(p:Bool → ℕ)(span:U → ℕ)(lag:U → Bool → ℕ):Prop:=
    let refund:=WilsonReceivedChronologicalRosterRanks.restored arity pole wanted
    let requested:=WilsonReceivedChronologicalRosterRanks.crop arity refund
    let depth:=WilsonReceivedChronologicalRosterRanks.infrared subjects refund
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
      V.paid=R.metals.O ∧ V.anchor=anchor ∧
      ∀(program:XSpace.Run)(stage:ℕ)(band:WilsonPositionProgramReporterBand.Band R program stage)
        (v:WilsonIndependentCapturedPages.Stop R program band o depth),
      ∃floor:ℕ,∀t f:ℕ,let c:=band.reporter+t
        floor ≤ c → c+2 ≤ f → 0 < v.date t → v.date t ≤ c →
        R.family.S.a c / R.family.S.a f ≤ (L.clock.hatBeta f)^window →
        L.S.scale c-L.S.scale (v.date t) ≤ 4*(2*(depth:ℝ)+1)*Real.log (regulatorRun R.family c 0 c)⁻¹ →
        let K:=WilsonInvariantActionPosition.berth R reserve f
        let m:=v.date t-1
        ∃old:o ≤ m, ∃walk:m+1 ≤ K-2, ∃ks:K-2+1+1=K,
        ∃source:Catalogue R subjects (K-2+1+1),∃uv:o ≤ m+1,∃vc:m+1<c,
        (∀per:ℕ,Trace.Physical.GermGraph.Opened R.family 0 o per ∧ Trace.Physical.GermGraph.Opened R.family 0 (m+1) per) ∧
        Open R simple k ask.school.pieces (ask.school.order+1) ask.load c ∧
        2≤L.clock.hatBeta c ∧ (eventually_atTop.mp (WilsonOriginalTwoFlatIRRows.nextClock R simple)).choose≤c ∧
        R.family.S.scale K-R.family.S.scale m ≤ (travel:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))) ∧
        WilsonReceivedChronologicalRosterMoney.Gate R subjects A travel pole P target refund refund wanted
          budget η η (WilsonReceivedChronologicalFixedRoseEnrolledCash.roof B caps) α (m+1) ∧
        ∀ᶠ per:ℕ in atTop,∀N:ℕ,∀valid:K ≤ N,
          let g:=regulatorRun R.family N per
          let rate:=(Real.sqrt (R.family.path.β N per (m+1)))^(1:ℝ)*B^n
          let money:=WilsonReceivedChronologicalFixedRoseEnrolledCash.roof B caps
          (WilsonOriginalTwoFlatIRCapturedCross.Quote R N per o (m+1) c refund depth (uv.trans vc.le) vc.le ∧
            1 ≤ money ∧ 0≤rate ∧ 0<g (m+1) ∧ g (m+1)≤1 ∧ g K≤1 ∧
            rate ≤ money*(3*(g c)⁻¹)^1 ∧ (∀i,caps i ≤ money*(3*(g c)⁻¹)^1) ∧
            rate ≤ money*(3*(g (m+1))⁻¹)^1 ∧ ∀i,caps i ≤ money*(3*(g (m+1))⁻¹)^1) ∧
          WilsonReceivedChronologicalRosterFork.Hired paid head subjects adult D pt caps φ requested A tol η tp ep
            school tube pieces physical p span lag book B o resident V draw m (K-2) old walk f
            ((WilsonInvariantActionPosition.arrival R reserve f).1.le.trans ks.ge) rent source per N (ks.le.trans valid) ∧
          ∀pupil:WilsonReceivedChronologicalFixedPlaced.Purchased
            (per:=per) (V:=V) (draw:=draw) (rate:=(Real.sqrt (R.family.path.β N per (m+1)))^(1:ℝ)*B^n)
            (allowance:=1) power P book (resident N (old.trans ((Nat.le_succ m).trans (walk.trans ((Nat.le_succ _).trans ((Nat.le_succ _).trans (ks.le.trans valid))))))) κ pt (K-2+1+1) m (ks.le.trans valid)
            (fun l=>base B caps power (L.clock.hatBeta (l+1))) old φ caps A target η,
          WilsonReceivedChronologicalRosterInterior.Paid
            (per:=per) (V:=V) (draw:=draw) (rate:=(Real.sqrt (R.family.path.β N per (m+1)))^(1:ℝ)*B^n)
            (allowance:=1) power P book (resident N (old.trans ((Nat.le_succ m).trans (walk.trans ((Nat.le_succ _).trans ((Nat.le_succ _).trans (ks.le.trans valid))))))) κ pt (K-2+1+1) m (ks.le.trans valid)
            (fun l=>base B caps power (L.clock.hatBeta (l+1))) old caps A target η pupil

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)
    {arity:ℕ}(head:Fin arity)(subjects:Fin arity → ℕ)(adult:∀i,0<subjects i)(D:Fin arity → ℕ)(pt:Fin arity → Chamber)
    (caps:Fin arity → ℝ)(nonneg:∀v,0 ≤ caps v)(hk:∀v,subjects v < D v)
    (rent:∀i,‖WilsonReceivedCanonicalSocketSeed.present D i‖≤caps i)(φ:Test arity)(reserve window wanted pole:ℕ)(budget α:ℝ)(bp:0≤budget)(slow:WilsonWindowReportingPace.Slow R.kit)(tol η:ℝ)(tp:0 < tol)(ep:0 < η)(school:ℕ)(tube:LinkTube G)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (pieces physical:ℕ)(p:Bool → ℕ)(span:U → ℕ)(lag:U → Bool → ℕ):
    ∃A travel:ℕ, Admitted paid paths head subjects adult D pt caps rent φ reserve window wanted pole A travel budget α tol η tp ep school tube pieces physical p span lag :=by
  classical
  let base:=WilsonReceivedChronologicalRosterRanks.restored arity pole wanted
  let Q:=WilsonReceivedChronologicalRosterRanks.crop arity base
  let horizon:=WilsonReceivedChronologicalRosterRanks.infrared subjects base
  have positive:0<horizon:=(WilsonReceivedChronologicalRosterRanks.original R subjects pole wanted).2.2.2.1
  obtain ⟨A,issued⟩:=WilsonReceivedChronologicalRosterFunded.original paid paths head subjects adult D pt caps
    nonneg hk rent φ reserve window horizon Q slow tol η tp ep school tube ready positive pieces physical p span lag
  obtain ⟨travel,cut,sized⟩:=WilsonReceivedChronologicalRosterSpan.original R simple slow reserve window horizon
  refine ⟨A,travel,?_⟩
  unfold Admitted
  intro refund requested depth n front k κ power target P menu ask L clock0
  obtain ⟨book,price,B,one,cohort⟩:=issued
  have funded:=WilsonReceivedChronologicalRosterSettled.before R simple subjects A travel pole wanted budget η η
    (WilsonReceivedChronologicalFixedRoseEnrolledCash.roof B caps) α bp
  refine ⟨book,price,B,one,?_⟩
  obtain ⟨ear,ears⟩:=eventually_atTop.mp (Trace.Physical.GermGraph.open_late R.family simple 0)
  filter_upwards [cohort,eventually_ge_atTop ear] with o entered earOpen
  obtain ⟨firm,opened,resident,quiet,seasons⟩:=entered
  refine ⟨firm,opened,resident,quiet,?_⟩
  filter_upwards [seasons] with anchor selected
  obtain ⟨V,draw,metal,based,uses⟩:=selected
  refine ⟨V,draw,metal,based,?_⟩
  intro world stage band v
  obtain ⟨floor,bought⟩:=uses world stage band v refund
  obtain ⟨start,prices⟩:=eventually_atTop.mp ((WilsonMovingForkCofinalStops.original R v).eventually funded)
  refine ⟨max (max floor cut) (band.reporter+start),?_⟩
  intro t f c late cf pos vc mesh span' K m
  have lower:max floor cut≤c:=(le_max_left ..).trans late
  have openedAt:=bought t f ((le_max_left ..).trans lower) cf pos vc mesh span'
  obtain ⟨old,walk,ks,archive,uv,strict,gate,big,clocked,records⟩:=openedAt
  have cutC:cut≤c:=(le_max_right ..).trans lower
  have due:band.reporter+start≤c:=(le_max_right ..).trans late
  have age:m+1=v.date t:=by dsimp [m];omega
  have extent:= (sized f c (by omega) cutC (v.date t) c 0 pos (by omega) vc le_rfl mesh span').2
  refine ⟨old,walk,ks,archive,uv,strict,fun per=>⟨ears o earOpen per,ears (m+1) (earOpen.trans uv) per⟩,
    gate,big,clocked,?_,?_,records⟩
  · simpa only [age] using extent
  · rw [age]
    exact prices t (by dsimp [c] at due;omega)

end YM.Integration.WilsonReceivedChronologicalRosterCertified
end
