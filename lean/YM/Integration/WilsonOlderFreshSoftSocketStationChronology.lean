import YM.Integration.WilsonOlderFreshSoftSocketStationWidths
import YM.Integration.WilsonOlderFreshSoftSocketStationNatural

/-! Separate the planting and return dates for the seven measured fields. The cofinal intermediate stop precedes the return width and the cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationChronology
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

def Sale (D:Fin 3→ℕ)(p q order width travel:ℕ)(ξ η δ opt τ radius:ℝ)(m C:Fin 3→ℝ)
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
        (per K c:ℕ),let w₀:=WilsonOlderFreshSoftSocketStationNatural.date R (depth R width ξ η τ δ m q) c
      v≤B.W.k→∀(kK:B.W.k≤K),v≤w₀→∀(ck:c≤K)(live:K<N),v+1≤K→8≤(road).clock.hatBeta K→
      R.family.S.a B.W.k/R.family.S.a K≤(road).clock.hatBeta B.W.k^width→
      R.family.S.a v/R.family.S.a K≤(road).clock.hatBeta v^travel→
      R.family.S.scale K-R.family.S.scale v≤opt*(1+Real.log ((road).clock.hatBeta (v+1)))→
      Hearing R D p q width ξ δ η m C (group F Jr Z B actual) r.val order (amount F Jr Z B)
        (started r B due actual).1 v N per K c w₀ V draw kK ck live ∧
      Paired R D p q order η C (group F Jr Z B actual) r.val (amount F Jr Z B)
          (started r B due actual).1 v N per K c w₀ V draw kK ck live

theorem original (u:G.ColorIndex)(paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R crop W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(room:Room (prepared s) R simple)
    (slow:WilsonWindowReportingPace.Slow R.kit)(bliss:Bliss F l z hier)(lead:Leading F Jr)(obedient:∀d:ℕ,∀ᶠr in trail,Frame.obedient F hier (Jr r) d):
    ∃(C:Fin 3→ℝ)(e:Fin 3→ℕ),(∀i,1≤C i) ∧ ∀(D:Fin 3→ℕ), (∀i,grade i<D i) →
    ∀(q order width:ℕ)(τ ξ δ η:ℝ),0<τ→0<ξ→0<δ→0<η→
    let m:Fin 3→ℝ:=fun i=>(e i:ℝ)
    let p:=7+(q+overhead R width ξ η δ m)+2
    let loss:=depth R width ξ η τ δ m q
    Tendsto (WilsonOlderFreshSoftSocketStationNatural.date R loss) atTop atTop ∧
    ∀(travel:ℕ)(opt:ℝ),0≤opt→∃radius:ℝ,0<radius ∧ ∃started:Started F Jr Z (l:=l) (hier:=hier) (z:=z) order η radius,
      Sale F Jr Z D p q order width travel ξ η δ opt τ radius m C started s simple:=by
  have quote:OPE.Therm.Poetry road:=by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,money,_⟩:=paid.originalSchool
    exact money.2.1.paid.stoves
  have cap(j:ℕ):1≤((road).budget j).supportExponent:=by rw [paid.support j];norm_num
  obtain ⟨C,e,C1,sales⟩:=WilsonOlderFreshSoftSocketStationPair.original F Jr Z simple bliss lead obedient
    (WilsonOlderFreshSoftRoseMarket.physical paid) cap quote
  refine ⟨C,e,C1,?_⟩
  intro D fit q order width τ ξ δ η tp xp dp ep m p loss
  have pos:0≤loss:=by
    dsimp [loss,WilsonOlderFreshSoftSocketStationStops.depth]
    positivity
  refine ⟨(WilsonOlderFreshSoftSocketStationNatural.elected R simple slow loss).1,?_⟩
  intro travel opt op
  let target:=q+overhead R width ξ η δ m
  have enough:p+1≤Burn.horizon (p+1):=by unfold Burn.horizon;omega
  obtain ⟨P,course,survey,issued⟩:=WilsonOlderFreshSoftSocketFigureCurve.original u paid paths room D fit
    (p+1) p target travel enough (le_refl _) opt τ δ op tp dp
  have measured:=WilsonOlderFreshSoftSocketStationWidths.sourced (ord:=ord) (hier:=hier) R simple width travel xp dp ep
  have separate:=WilsonOlderFreshSoftSocketStationWidths.stopped (ord:=ord) (hier:=hier) (τ:=τ) R simple width xp dp ep
  obtain ⟨dateFloor,timed⟩:=eventually_atTop.mp (WilsonOlderFreshSoftSocketStationNatural.original R simple slow loss pos travel)
  obtain ⟨age,stops⟩:=eventually_atTop.mp ((((issued.and measured).and separate).and (eventually_ge_atTop survey)).and (eventually_ge_atTop course))
  obtain ⟨radius,rp,wages⟩:=Metric.mem_nhdsWithin_iff.mp (sales order ep)
  have inside(r:{r:ℝ // 0<r ∧ r<radius}):r.val∈Metric.ball (0:ℝ) radius ∩ Set.Ioi 0:=
    ⟨by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos r.property.1] using r.property.2,r.property.1⟩
  have start:Started F Jr Z (l:=l) (hier:=hier) (z:=z) order η radius:=
    fun r _ B due actual=>(wages (inside r) B due actual).1
  refine ⟨radius,rp,start,P,course,max age dateFloor,?_⟩
  intro v aged
  obtain ⟨⟨⟨⟨house,hear⟩,stopped⟩,late⟩,coarse⟩:=stops v ((le_max_left ..).trans aged)
  obtain ⟨V,draw,scheme,heat,anchor,both,tables,enter⟩:=house
  refine ⟨V,draw,scheme,heat,anchor,both,tables,?_⟩
  intro N vN
  obtain ⟨Y,grown,opened⟩:=enter N vN
  refine ⟨Y,grown,?_⟩
  intro school day
  obtain ⟨same,file⟩:=opened school day
  refine ⟨same,?_⟩
  intro r T B due actual per K c w₀ vk kK first ck live away warm planted band span
  have second:w₀≤c:=WilsonOlderFreshSoftSocketStationNatural.earlier R loss c
  have guard:dateFloor≤c:=((le_max_right age dateFloor).trans aged).trans (first.trans second)
  have gap:=(timed c guard K N per ck live.le (WilsonOlderFreshSoftSocketStationDate.width R simple (first.trans second) band)).1
  obtain ⟨_,pos,cash⟩:=wages (inside r) B due actual
  have quoted(i:Fin 3):amount F Jr Z B i≤C i*((road).clock.hatBeta K)^(m i):=by
    simpa only [m,Real.rpow_natCast] using cash K kK i
  constructor
  · exact hear D p q survey order N per K c w₀ opt (group F Jr Z B actual) B.checked r.val B.active vk
      (late.trans vk) kK first second ck live away warm planted band span V draw m C (amount F Jr Z B)
      (start r B due actual).1 (fun _=>Nat.cast_nonneg _) (fun i=>zero_le_one.trans (C1 i)) pos quoted
      (file per K (vk.trans kK) live.le band)
  · exact stopped D p q course order N per K c w₀ opt (group F Jr Z B actual) B.checked r.val B.active vk
      (coarse.trans vk) kK first second ck live away warm planted span V draw m C (amount F Jr Z B)
      (start r B due actual).1 (fun _=>Nat.cast_nonneg _) (fun i=>zero_le_one.trans (C1 i)) pos quoted gap both

end YM.Integration.WilsonOlderFreshSoftSocketStationChronology
end
