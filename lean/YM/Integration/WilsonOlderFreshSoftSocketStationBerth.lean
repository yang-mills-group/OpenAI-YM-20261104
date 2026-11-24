import YM.Integration.WilsonOlderFreshSoftSocketStationChronology
import YM.Integration.WilsonMovingForkOpticalStops

/-! The measured planting date is the first retained fine mesh for the original physical station. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationBerth
open Function Filter Finset Lattice Laurent Bloch Precision Wilson RG Source Labels Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Winding WilsonCoeffUV.Soil WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PertExtension NativeCurvatureTensor
open OriginalMarkedSourceComet WilsonReceivedFixedDigitHistory
open WilsonOlderFreshSoftFigureReading (upper reading)
open WilsonOlderFreshSoftStops (scalarOnly)
open WilsonOlderFreshSoftTrialCharge (power bill wages)
open WilsonOriginalPublicTrialInput (vector)
open scoped Classical BigOperators Topology
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar WilsonOriginalAllOrderCourse WilsonOriginalOpticalSchedule
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Iron
open QuadraticLocal QuadraticLocal.Mentor
open WilsonIndependentCollarRootedWidth
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge} {a:Axis} {simple:G.Simple} {ε:ℝ}
variable {s:WilsonOriginalAllOrderCourse.Schedule G} {R:Run G} {crop:Campaign R} {W:Campaign.Pillars R crop}

open WilsonOlderFreshSoftRoseCourse (grade seat Hearing)
open WilsonOlderFreshSoftTrialCharge (power bill)


open WilsonOlderFreshSoftRoseMarket (Probe row scaled)
open WilsonOlderFreshSoftRoseSecant (deficit actual)
open WilsonNeutralOffsetCutoff (named)
open WilsonThermometerAlignedCells (atOrigin)

variable (R) (A₀:WilsonPositionThermometerCapStation.Group R.family 6)
local notation "Faces" => Finset (Fin 3)
local notation "Sites" N:max per:max => Site (R.family.side N per)


open WilsonOriginalPublicFixedCourse (sites digits home)
open WilsonOlderFreshSoftRoseMesh (filed table fare)
open WilsonMaxwellThermometerNominatedSecant (bill)

open WilsonOlderFreshSoftRoseNodes (TestAt enrolled Covered)
open WilsonOlderFreshSoftTrialCut (source)
open WilsonOlderFreshSoftMoment (mixed)

open WilsonOlderFreshSoftRoseIncome (Stock)
open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusAttendanceStation
open WilsonVacuumPreResetDatedDeposit (Issued)
open PertExtension.Series WilsonCoeffUV.Blue.Cameo
open WilsonOriginalAllOrderCourse
open WilsonOriginalOccupiedForestIntegral
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonVacuumPreResetDatedCourse
open WilsonReportingAbsoluteInletForecastBooks
open WilsonOlderFreshSoftSocketFitted (residual)
open WilsonOlderFreshSoftSocketOptical (fixed)
open WilsonOlderFreshSoftSocketCensus (fee)
open WilsonOriginalPublicTrialInput (fitted)
open WilsonOriginalMicroscopicGuardedPageSchool (Indexed)
open WilsonIndependentCollarCensusCourse
open Filter


open WilsonOlderFreshSoftSocketFigureCurve (Bought)
open WilsonOlderFreshSoftSocketVane (quotaFare)
open WilsonOriginalMicroscopicGuardedGridSchool (Finished)
open WilsonOriginalPublicTrialInput (fitted)
open WilsonPositionThermometerCapStation (Group)
open Cells Extraction Climb Trace Trace.Pilot PhysMS

open WilsonOlderFreshSoftSocketStationSale (Hearing overhead)
open WilsonOlderFreshSoftSocketStationPair (amount)
open WilsonOriginalTwoFlatRoseBook (group)
open WilsonMovingForkWindowBooks (Priced)
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare


open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
open MS MS.Land FVA2 FVA2.Register

variable {R} {ord:Extraction.Order}{S:Table R.family.book} (F:Final R.family ord S)
  {l:Ultrafilter (ℕ×ℕ)} {hier:(Bel R.family.book).Hierarchy} {z:Trace.Terrace.Arch R.family}
  (Jr:ℝ→tower S)(Z:WilsonPrescription G)
local notation "Book_" => WilsonOriginalTwoFlatPublicBooks.Book F (l:=l) hier z 6
local notation "road" => R.family.path.levels

open WilsonOlderFreshSoftSocketStationCampaign (Started)
open WilsonOlderFreshSoftSocketStationStops (depth Paired)

open WilsonInvariantActionPosition (berth arrival)

def Quoted (D:Fin 3→ℕ)(p q order t roomWidth descent:ℕ)(ξ η δ opt τ radius:ℝ)(m C:Fin 3→ℝ)
    (started:Started F Jr Z (l:=l) (hier:=hier) (z:=z) order η radius)
    (schedule:WilsonOriginalAllOrderCourse.Schedule G)(simple:G.Simple):Prop:=
  ∃(P:Credit)(course age:ℕ),∀v,age≤v→∃(V:Realm G (p+1) Credit.leanC)(draw:V.draws=road),
    V.paid=R.metals.O ∧ V.y=zz road ∧ V.anchor=v ∧ Covered R D p v course V draw opt τ ∧
    (∀t:Faces,t.Nonempty→Stock R D p v course V draw opt τ t) ∧
    ∀N:ℕ,v≤N→∃Y:ℕ→SeriesA G,
      (∀j,v≤j→j≤N→∃σ:ℝ,0<σ ∧ σ⁻¹≤zz road j ∧ Issued R N j (Burn.horizon (p+1)) (Y j) σ
          (P.buy (zz road j)+zz road j*(road).clock.loopCap j)) ∧
      ∀(school:Syl.School (p+1))(day:Day (prepared schedule) R simple school v N),
      Agrees R N v (Burn.horizon (p+1)) Y day.π day.Γ ∧
      ∀(r:{r:ℝ // 0<r ∧ r<radius}){T:ℕ}(B:Book_ T r.val)(due:Priced F B)(actual:Next.UVStress.Lifts R.family B.k)
        (per c front:ℕ),let j:=B.W.k
      let K:=berth R t j
      let kK:j≤K:=(arrival R t j).1.le
      let w₀:=WilsonOlderFreshSoftSocketStationNatural.date R (depth R (t+1) ξ η τ δ m q) c
      v≤front→front≤j→v≤w₀→∀(ck:c≤K)(live:K<N),
      R.family.S.a front/R.family.S.a j≤(road).clock.hatBeta j^roomWidth→
      R.family.S.scale front-R.family.S.scale v≤4*(2*(descent:ℝ)+1)*Real.log (regulatorRun R.family N per front)⁻¹→
      Hearing R D p q (t+1) ξ δ η m C (group F Jr Z B actual) r.val order (amount F Jr Z B)
        (started r B due actual).1 v N per K c w₀ V draw kK ck live ∧
      Paired R D p q order η C (group F Jr Z B actual) r.val (amount F Jr Z B)
          (started r B due actual).1 v N per K c w₀ V draw kK ck live

theorem original (u:G.ColorIndex)(paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R crop W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(room:Room (prepared s) R simple)
    (slow:WilsonWindowReportingPace.Slow R.kit)(bliss:Bliss F l z hier)(lead:Leading F Jr)(obedient:∀d:ℕ,∀ᶠr in trail,Frame.obedient F hier (Jr r) d):
    ∃(C:Fin 3→ℝ)(e:Fin 3→ℕ),(∀i,1≤C i) ∧ ∀(D:Fin 3→ℕ), (∀i,grade i<D i) →
    ∀(q order t:ℕ)(τ ξ δ η:ℝ),0<τ→0<ξ→0<δ→0<η→
    let m:Fin 3→ℝ:=fun i=>(e i:ℝ)
    let p:=7+(q+overhead R (t+1) ξ η δ m)+2
    let loss:=depth R (t+1) ξ η τ δ m q
    Tendsto (WilsonOlderFreshSoftSocketStationNatural.date R loss) atTop atTop ∧
    ∀(roomWidth descent:ℕ),∃(opt radius:ℝ),0<radius ∧
      ∃started:Started F Jr Z (l:=l) (hier:=hier) (z:=z) order η radius,
        Quoted F Jr Z D p q order t roomWidth descent ξ η δ opt τ radius m C started s simple:=by
  obtain ⟨C,e,cash,openHouse⟩:=WilsonOlderFreshSoftSocketStationChronology.original F Jr Z u paid paths room slow bliss lead obedient
  refine ⟨C,e,cash,?_⟩
  intro D fit q order t τ ξ δ η tp xp dp ep m p loss
  obtain ⟨cofinal,traded⟩:=openHouse D fit q order (t+1) τ ξ δ η tp xp dp ep
  refine ⟨cofinal,?_⟩
  intro roomWidth descent
  obtain ⟨travel,clock⟩:=WilsonMovingForkOpticalStops.original R simple slow t roomWidth descent
  obtain ⟨rad,rp,started,bought⟩:=traded travel travel (Nat.cast_nonneg _)
  obtain ⟨P,course,threshold,issued⟩:=bought
  have fly:=WilsonAddressedCollarWindow.original R simple slow t (show (0:ℝ)<1 by norm_num)
  obtain ⟨first,grown⟩:=eventually_atTop.mp ((clock.and fly).and ((Next.Rank.Station.hat_rate road simple).eventually_ge_atTop 8))
  refine ⟨travel,rad,rp,started,P,course,max threshold first,?_⟩
  intro v aged
  obtain ⟨V,draw,scheme,heat,anchor,both,stock,file⟩:=issued v ((le_max_left ..).trans aged)
  refine ⟨V,draw,scheme,heat,anchor,both,stock,?_⟩
  intro N vn
  obtain ⟨Y,exposed,calendar⟩:=file N vn
  refine ⟨Y,exposed,?_⟩
  intro school day
  obtain ⟨coins,sale⟩:=calendar school day
  refine ⟨coins,?_⟩
  intro r T B due actual per c front j K kK w before reach vw ck live captured reg
  have vj:=before.trans reach
  obtain ⟨⟨distance,fine⟩,hot⟩:=grown j (((le_max_right ..).trans aged).trans vj)
  have cold:8≤(road).clock.hatBeta K:=hot.trans (WilsonReflectedOpticalStock.monotone R simple kK)
  have planted:R.family.S.a j/R.family.S.a K≤(road).clock.hatBeta j^(t+1):=by
    simpa only [Real.rpow_one,pow_succ] using fine.2.2
  obtain ⟨far,span⟩:=distance front v N per reach before ((reach.trans kK).trans live.le) captured reg
  exact sale r B due actual per K c vj kK vw ck live (by have h:=fine.1;omega) cold planted far span

end YM.Integration.WilsonOlderFreshSoftSocketStationBerth
end
