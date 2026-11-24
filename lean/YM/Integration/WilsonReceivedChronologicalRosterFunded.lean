import YM.Integration.WilsonReceivedChronologicalRosterForkCampus
import YM.Integration.WilsonReceivedChronologicalRosterTariff
import YM.Integration.WilsonReceivedChronologicalRosterInteriorPortal
import YM.Integration.WilsonReceivedChronologicalRosterSpan
import YM.Integration.WilsonMovingForkCofinalStops
import YM.Integration.WilsonInvariantActionPosition

/-! The before-programme roster on its actual moving physical capture and on arbitrary independently placed ports. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterFunded
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

private theorem moved (model:Run G) {N per o v v' c P infrared:ℕ}(same:v=v')(home:o≤c)(old:v≤c)(younger:v'≤c)
    (bought:WilsonOriginalTwoFlatIRCapturedCross.Quote model N per o v' c P infrared home younger):
    WilsonOriginalTwoFlatIRCapturedCross.Quote model N per o v c P infrared home old:=by
  subst v'
  exact @bought

def Admitted (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)
    {arity:ℕ}(head:Fin arity)(subjects:Fin arity → ℕ)(adult:∀i,0<subjects i)(D:Fin arity → ℕ)(pt:Fin arity → Chamber)
    (caps:Fin arity → ℝ)
    (rent:∀i,‖WilsonReceivedCanonicalSocketSeed.present D i‖≤caps i)(φ:Test arity)(reserve window depth requested A:ℕ)(tol η:ℝ)(tp:0 < tol)(ep:0 < η)(school:ℕ)(tube:LinkTube G)
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
      V.paid=R.metals.O ∧ V.anchor=anchor ∧
      ∀(program:XSpace.Run)(stage:ℕ)(band:WilsonPositionProgramReporterBand.Band R program stage)
        (v:WilsonIndependentCapturedPages.Stop R program band o depth)(degree:ℕ),
      ∃floor:ℕ,∀t f:ℕ,let c:=band.reporter+t
        floor ≤ c → c+2 ≤ f → 0 < v.date t → v.date t ≤ c →
        R.family.S.a c / R.family.S.a f ≤ (L.clock.hatBeta f)^window →
        L.S.scale c-L.S.scale (v.date t) ≤ 4*(2*(depth:ℝ)+1)*Real.log (regulatorRun R.family c 0 c)⁻¹ →
        let K:=WilsonInvariantActionPosition.berth R reserve f
        let m:=v.date t-1
        ∃old:o ≤ m, ∃walk:m+1 ≤ K-2, ∃ks:K-2+1+1=K,
        ∃source:Catalogue R subjects (K-2+1+1),∃uv:o ≤ m+1,∃vc:m+1<c,
        Open R simple k ask.school.pieces (ask.school.order+1) ask.load c ∧
        2≤L.clock.hatBeta c ∧ (eventually_atTop.mp (WilsonOriginalTwoFlatIRRows.nextClock R simple)).choose≤c ∧
        ∀ᶠ per:ℕ in atTop,∀N:ℕ,∀valid:K ≤ N,
          let g:=regulatorRun R.family N per
          let rate:=(Real.sqrt (R.family.path.β N per (m+1)))^(1:ℝ)*B^n
          let money:=WilsonReceivedChronologicalFixedRoseEnrolledCash.roof B caps
          (WilsonOriginalTwoFlatIRCapturedCross.Quote R N per o (m+1) c degree depth (uv.trans vc.le) vc.le ∧
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
    (rent:∀i,‖WilsonReceivedCanonicalSocketSeed.present D i‖≤caps i)(φ:Test arity)(reserve window depth requested:ℕ)(slow:WilsonWindowReportingPace.Slow R.kit)(tol η:ℝ)(tp:0 < tol)(ep:0 < η)(school:ℕ)(tube:LinkTube G)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)(positive:0<depth)
    (pieces physical:ℕ)(p:Bool → ℕ)(span:U → ℕ)(lag:U → Bool → ℕ):
    ∃A:ℕ, Admitted paid paths head subjects adult D pt caps rent φ reserve window depth requested A tol η tp ep school tube pieces physical p span lag :=by
  classical
  obtain ⟨A,source⟩:=WilsonReceivedChronologicalRosterForkCampus.original paid paths head subjects adult D pt caps nonneg
    hk rent φ reserve window depth requested slow tol η tp ep school tube pieces physical p span lag
  refine ⟨A,?_⟩
  unfold Admitted
  intro n front k κ power target P menu ask L clock0
  obtain ⟨book,price,B,one,registered⟩:=source
  refine ⟨book,price,B,one,?_⟩
  filter_upwards [registered,eventually_ge_atTop (R.family.ref 0)] with o enrolled ref
  obtain ⟨firm,opened,resident,quiet,seasons⟩:=enrolled
  refine ⟨firm,opened,resident,quiet,?_⟩
  filter_upwards [seasons] with anchor selected
  obtain ⟨V,draw,metal,based,usable⟩:=selected
  refine ⟨V,draw,metal,based,?_⟩
  intro world stage band v degree
  obtain ⟨floor,scheduled⟩:=usable world stage band v
  obtain ⟨oneFee,earned⟩:=WilsonReceivedChronologicalRosterTariff.original R simple k ask.school.pieces
    (ask.school.order+1) ask.load B one caps (2*A) slow ready world band v positive ref degree
  obtain ⟨start,bills⟩:=eventually_atTop.mp earned
  refine ⟨max floor (band.reporter+start),?_⟩
  intro t f c late cf pos vc ratio span' K m
  have structural:=scheduled t f ((le_max_left ..).trans late) cf pos vc ratio span'
  obtain ⟨old,walk,ks,archive,entitled⟩:=structural
  have reached:band.reporter+start≤c:=(le_max_right ..).trans late
  obtain ⟨uv,strict,gate,big,clocked,fees⟩:=bills t (by dsimp [c] at reached;omega)
  have date:m+1=v.date t:=by dsimp [m];omega
  have heard:o ≤ m+1:=old.trans (Nat.le_succ m)
  have before:m+1<c:=date.trans_lt strict
  refine ⟨old,walk,ks,archive,heard,before,gate,big,clocked,?_⟩
  filter_upwards [entitled] with per paidAt
  intro N valid g rate money
  have classroom:=paidAt N valid
  refine ⟨?_,classroom⟩
  obtain ⟨actor,_,_,_,_,_,_,_,_,_,mesh,_⟩:=classroom.1
  have aligned:R.family.S.a (v.date t)/R.family.S.a K≤(L.clock.hatBeta (v.date t))^(2*A):=by
    have step:v.date t-1+1=v.date t:=by omega
    simpa only [ks,step] using mesh
  have fine:f<K:=(WilsonInvariantActionPosition.arrival R reserve f).1
  obtain ⟨quote,rent₀,gp,cold,coldK,out,high,out₁,high₁⟩:=fees (per:=per) (by omega:c<K) valid aligned
  dsimp only [g,rate,money]
  refine ⟨moved R date (heard.trans before.le) before.le strict.le (@quote),oneFee,?_⟩
  rw [date]
  exact ⟨rent₀,gp,cold,coldK,out,high,out₁,high₁⟩

end YM.Integration.WilsonReceivedChronologicalRosterFunded
end
