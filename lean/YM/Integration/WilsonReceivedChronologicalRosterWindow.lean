import YM.Integration.WilsonReceivedChronologicalFixedRoseGridCampus
import YM.Integration.WilsonReceivedChronologicalRosterCourse

/-! One paid room and original marked clock for the measured pair, before the physical period and cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterWindow
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
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS
open Analysis XSpace Cells Table Spec Extraction
open WilsonOriginalTwoFlatIRCapturedCross (Quote)
open WilsonReceivedChronologicalFixedCellFee (capture factor)
open WilsonAddressedPublicFirstRoseGeometry (Fits)
open WilsonPositionProgramReporterBand (Band)
open Pert.Asymptotics
open WilsonAddressedPublicFirstRoseSchedule (allowance)
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

def Slot (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    {arity:ℕ}(head:Fin arity)(subjects:Fin arity→ℕ)(adult:∀i,0<subjects i)(D:Fin arity → ℕ)(pt:Fin arity → Chamber)
    (caps:Fin arity → ℝ)
    (φ:Test arity)(requested A:ℕ)(tol η:ℝ)(tp:0 < tol)(ep:0 < η)(school:ℕ)(tube:LinkTube G)
    (pieces physical:ℕ)(p:Bool → ℕ)(span:U → ℕ)(lag:U → Bool → ℕ):=
    let n:=arity
    let front:Fin n:=head
    let k:=subjects
    let κ:∀v:Fin arity,Knob (D v):=fun v=>contact (D v)
    let power:=fun _:Fin arity=>0
    let target:=WilsonOriginalReflectedFirstTerms.order R subjects requested
    let P:=target+1
    let menu:=terms k power P
    let ask:=programme k power P
    let L:=R.family.path.levels
    let firstPeriod:=appointment R simple k D pt (fun _=>4) tube ask.order ask.order menu.target menu.precision
      (seller G) (financed paid) (WilsonAddressedPublicFirstRanks.original k P).2.2.2.1
    fun (book:WilsonOriginalCensusPhysicalAttendance.Room (prepared s) R simple) (B:ℝ)
      (o:ℕ) (resident:(N:ℕ) → o ≤ N → Day (prepared s) R simple ask.school o N)
      (V:Realm G (menu.order+1) Credit.leanC) (draw:V.draws=L)
      (m j:ℕ) (old:o ≤ m) (mj:m+1 ≤ j) (per N:ℕ) (valid:j+1+1 ≤ N) =>
      let K:=j+1+1
      let δ:ℝ:=1
        let H:=Real.sqrt (R.family.path.β N per (m+1))
        let rate:=H^δ*B^n
        let oldDay:=resident N (old.trans ((Nat.le_succ m).trans (mj.trans ((Nat.le_succ j).trans ((Nat.le_succ (j+1)).trans valid)))))
        ∃classroom:Purchased (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=δ) power P book oldDay κ pt K m valid
          (fun j=>base B caps power (L.clock.hatBeta (j+1))) old φ caps A target η,
        Sold (R:=R) (simple:=simple) (d:=k) (P:=P) (m:=o) (first:=m) (j:=j) (N:=N) (per:=per)
          (schedule:=s) (A:=A) (V:=V) (draw:=draw) (rate:=rate) (allowance:=δ) (φ:=φ) (caps:=caps) (promised:=target) (θ:=η)
          (school:=book) (day:=oldDay) (live:=valid) (lens:=D) (pt:=pt)
          (toll:=fun l=>base B caps power (L.clock.hatBeta (l+1))) (old:=old)
          (classroom:=classroom) (adult:=adult) η ∧
        WilsonIndependentConditionedLocatedFirstPanels.Sold (R:=R) (simple:=simple) (d:=k) (P:=P) (m:=o) (first:=m) (j:=j) (N:=N) (per:=per)
          (schedule:=s) (A:=A) (V:=V) (draw:=draw) (rate:=rate) (allowance:=δ) (φ:=φ) (caps:=caps) (promised:=target) (θ:=η)
          (school:=book) (day:=oldDay) (live:=valid) (lens:=D) (pt:=pt)
          (toll:=fun l=>base B caps power (L.clock.hatBeta (l+1))) (old:=old)
          (classroom:=classroom) (adult:=adult) η ∧
        WilsonIndependentCollarDatedTeachers.At s R simple V D k (Burn.horizon ask.vac) school δ tube pieces physical p span lag m ∧
        V.anchor ≤ m+1 ∧
        WilsonOriginalCensusSparseRosterOpening.first R simple tube k k (charges power) menu.order menu.order
          menu.target menu.precision menu.enough ≤ m+1 ∧
        Period (R:=R) (V:=V) (per:=per) (grades:=k) power P κ pt K m caps ∧
        WilsonOriginalOneArmCurrentClock.first R simple k power P (2*A) tol η tp ep (Nat.zero_lt_of_lt front.isLt) ≤ m ∧
        R.family.S.a (m+1)/R.family.S.a K ≤ (L.clock.hatBeta (m+1))^(2*A) ∧
        WilsonAddressedPublicFirstOrigin.ceiling R k ≤ menu.order ∧
        WilsonOriginalReflectedFirstTerms.At R simple k P (2*A) tol η tp ep (m+1) (K-2) ∧
        WilsonIndependentCollarDatedTeachers.At s R simple V D k (Burn.horizon ask.vac) school δ tube
          pieces physical p span lag (K-2) ∧
        firstPeriod.first ≤ K-2+1 ∧
        firstPeriod.period (K-2+1)
          (WilsonAddressedPublicFirstExtent.extent V.draws (0:Fin arity → Cover) m (K-2-m)) ≤ per

variable {reg:Extraction.Order}{S:Table R.family.book}(F:Final R.family reg S)
  {l:Ultrafilter (ℕ×ℕ)} {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}

private theorem moved (model:Run G) {N per o v v' c P infrared:ℕ}(same:v=v')(home:o≤c)(old:v≤c)(younger:v'≤c)
    (bought:WilsonOriginalTwoFlatIRCapturedCross.Quote model N per o v' c P infrared home younger):
    WilsonOriginalTwoFlatIRCapturedCross.Quote model N per o v c P infrared home old:=by
  subst v'
  exact @bought

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)
    {arity:ℕ}(head:Fin arity)(subjects:Fin arity→ℕ)(adult:∀i,0<subjects i)(D:Fin arity → ℕ)(pt:Fin arity → Chamber)
    (caps:Fin arity → ℝ)(nonneg:∀v,0 ≤ caps v)(hk:∀v,subjects v < D v)
    (φ:Test arity)(requested:ℕ)(tol η:ℝ)(tp:0 < tol)(ep:0 < η)(school:ℕ)(tube:LinkTube G)
    (pieces physical:ℕ)(p:Bool → ℕ)(span:U → ℕ)(lag:U → Bool → ℕ)
    (bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (bookDegree publicFee h reserve infrared:ℕ)(depth:0 < infrared)(labels:Fin arity → Fin (bookDegree+1))
    {rad:ℝ}(books:(s:{s:ℝ // 0 < s ∧ s < rad}) → WilsonOriginalTwoFlatPublicBooks.Book F (l:=l) H z bookDegree publicFee s.val):
    let A:=WilsonAddressedPublicFirstRoseSchedule.allowance R simple slow publicFee h reserve infrared
    let n:=arity
    let _front:Fin n:=head
    let k:=subjects
    let _κ:∀v:Fin arity,Knob (D v):=fun v=>contact (D v)
    let power:=fun _:Fin arity=>0
    let target:=WilsonOriginalReflectedFirstTerms.order R subjects requested
    let P:=target+1
    let menu:=terms k power P
    let ask:=programme k power P
    let L:=R.family.path.levels
    let _firstPeriod:=appointment R simple k D pt (fun _=>4) tube ask.order ask.order menu.target menu.precision
      (seller G) (financed paid) (WilsonAddressedPublicFirstRanks.original k P).2.2.2.1
    ∃book:WilsonOriginalCensusPhysicalAttendance.Room (prepared s) R simple,
    ∃price:Credit,∃B:ℝ,1 ≤ B ∧ ∀ᶠo:ℕ in atTop,
      WilsonSingleHardRadius.first R simple ≤ o ∧
      WilsonOriginalCensusCanonicalAppointedClock.opening R simple (seller G) (financed paid) paths
        (Burn.horizon ask.vac) ≤ o ∧
      ∃resident:(N:ℕ) → o ≤ N → Day (prepared s) R simple ask.school o N,
      (∀N,∀live:o ≤ N,∃Z:ℕ → SeriesA G,QuietAt (resident N live) price Z) ∧
      ∀ᶠanchor:ℕ in atTop,∃V:Realm G (menu.order+1) Credit.leanC,∃draw:V.draws=L,
      V.paid=R.metals.O ∧ V.anchor=anchor ∧ ∀(world:XSpace.Run)(stage:ℕ)(run:WilsonPositionProgramReporterBand.Band R world stage)
      (v:WilsonIndependentCapturedPages.Stop R world run o infrared),0 < stage → R.family.ref 0 ≤ o → 
      ∀(powerOrder floor:ℕ),∀ᶠr in trail,∀ρ:Fin arity → {s:ℝ // 0 < s ∧ s < rad},
      (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) → 
      let f:=berth R 5 (univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k)
      let K:=berth R reserve f
      let c:=WilsonReceivedChronologicalFixedCellFee.capture R φ r
      ∃w:ℕ,∃_hc:c=run.reporter+w,
        let m:=v.date w-1
        ∃_same:m+1=v.date w, ∃old:o ≤ m,∃lower:m+1 < c,∃_finer:c < f,∃_start:f < K,
        ∃walk:m+1 ≤ K-2,∃ks:K-2+1+1=K, floor+1 ≤ c ∧ stage ≤ m+1 ∧
        WilsonAddressedPublicFirstRoseGeometry.Fits R.family.S (WilsonAddressedPublicFirstSites.original R draw φ).choose r m f ∧
        WilsonAddressedPublicFirstRoseGeometry.Fits R.family.S (WilsonReceivedChronologicalFixedCellFee.factor R φ) r m f ∧
        WilsonAddressedPublicFirstRoseTicket.Receipt R (WilsonAddressedPublicFirstSites.original R draw φ).choose
          (WilsonReceivedChronologicalFixedCellFee.factor R φ) r (wilson z r) m f K c A ∧
        ∀ᶠper:ℕ in atTop,∀N:ℕ,∀valid:K ≤ N,
        let rate:= (Real.sqrt (R.family.path.β N per (m+1)))^(1:ℝ)*B^arity
        let C:=max (max 1 (B^arity)) (∑i,|caps i|)
        let g:=regulatorRun R.family N per
        WilsonOriginalTwoFlatIRCapturedCross.Quote R N per o (m+1) c powerOrder infrared ((old.trans (Nat.le_succ m)).trans lower.le) lower.le ∧
        1 ≤ C ∧ 0 ≤ rate ∧ 0 < g (m+1) ∧ g (m+1) ≤ 1 ∧ g K ≤ 1 ∧
        rate ≤ C*(3*(g c)⁻¹)^1 ∧ (∀i,caps i ≤ C*(3*(g c)⁻¹)^1) ∧
        rate ≤ C*(3*(g (m+1))⁻¹)^1 ∧ (∀i,caps i ≤ C*(3*(g (m+1))⁻¹)^1) ∧
        Slot paid head subjects adult D pt caps φ requested A tol η tp ep school tube pieces physical p span lag
          book B o resident V draw m (K-2) old walk per N (ks.le.trans valid):=by
  classical
  letI : Nonempty (Fin arity) := ⟨head⟩
  intro A n front k κ power target P menu ask L firstPeriod
  obtain ⟨book,price,B,one,cohort⟩:=WilsonReceivedChronologicalRosterCourse.original paid paths head subjects adult D pt caps nonneg hk
    φ requested A tol η tp ep school tube pieces physical p span lag
  obtain ⟨cpos,entry⟩:=WilsonReceivedChronologicalFixedRoseEnrolledCash.original R simple B one caps (2*A)
  obtain ⟨opened,cash⟩:=eventually_atTop.mp entry
  refine ⟨book,price,B,one,?_⟩
  filter_upwards [cohort] with o hired
  obtain ⟨hard,activated,resident,quiet,appointed⟩:=hired
  refine ⟨hard,activated,resident,quiet,?_⟩
  filter_upwards [appointed] with anchor enrollment
  obtain ⟨V,draw,metal,based,usable⟩:=enrollment
  refine ⟨V,draw,metal,based,?_⟩
  intro world stage run v positive ref powerOrder floor
  let Future(m:ℕ):Prop:=opened ≤ m+1 ∧ ∃old:o ≤ m,∀j:ℕ,∀mj:m+1 ≤ j,
    L.S.scale (j+1+1)-L.S.scale m ≤ (A:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))) → 
    ∀ᶠper:ℕ in atTop,∀N:ℕ,∀valid:j+1+1 ≤ N,
      Slot paid head subjects adult D pt caps φ requested A tol η tp ep school tube pieces physical p span lag book B o resident V draw m j old mj per N valid
  have later:∀ᶠm:ℕ in atTop,Future m:=by
    filter_upwards [usable 1 (by norm_num) le_rfl,eventually_ge_atTop opened] with m admitted old
    obtain ⟨prior,hits⟩:=admitted
    exact ⟨old.trans (Nat.le_succ m),prior,hits⟩
  have hp:=((WilsonAddressedPublicFirstSites.original R draw φ).choose_spec).choose
  have selected:=WilsonReceivedChronologicalFixedRoseGridStops.original F simple bliss slow ready world run v positive depth
    ref powerOrder floor φ hp bookDegree publicFee h reserve labels later books
  filter_upwards [selected] with r offered
  intro ρ crops minimum f K c
  obtain ⟨w,eq,uc,vc,date,uv,leStage,behind,readyAt,walk,ks,before,finer,start,fitA,fitB,ticket,quotes⟩:=offered ρ crops minimum
  let m:=v.date w-1
  have low:m+1 < c:=date.trans_lt before
  obtain ⟨paidHeat,ordinary,fees⟩:=readyAt
  have spanFit:L.S.scale (K-2+1+1)-L.S.scale m ≤ (A:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))):=by rw [ks];exact ticket.span
  refine ⟨w,eq,date,ordinary,low,finer,start,walk,ks,behind,date ▸ leStage,fitA,fitB,ticket,?_⟩
  filter_upwards [fees (K-2) walk spanFit] with per sold
  intro N valid rate C g
  have invoice:=sold N (ks.le.trans valid)
  obtain ⟨classroom,own,firstEdge,teacher,vt,rows,period,current,geometry,rank,elig,high,turn,board⟩:=invoice
  have mesh:L.S.a (m+1)/L.S.a K ≤ (L.clock.hatBeta (m+1))^(2*A):=by
    have align:K-2+1+1=K:=ks
    calc
      _=L.S.a (m+1)/L.S.a (K-2+1+1):=congrArg (fun t=>L.S.a (m+1)/L.S.a t) align.symm
      _ ≤ _:=geometry
  have bonds:=cash (m+1) paidHeat (per:=per) low.le (finer.le.trans start.le) valid mesh
  refine ⟨?_,cpos,bonds.1,bonds.2.1,bonds.2.2.1,bonds.2.2.2.1,bonds.2.2.2.2.1,bonds.2.2.2.2.2.1,
    bonds.2.2.2.2.2.2.1,bonds.2.2.2.2.2.2.2,?_⟩
  · have agree:m+1=v.date w:=date
    refine @moved _ R N per o (m+1) (v.date w) c powerOrder infrared agree _ _ vc ?_
    exact @quotes N per valid
  · exact ⟨classroom,own,firstEdge,teacher,vt,rows,period,current,geometry,rank,elig,high,turn,board⟩

end YM.Integration.WilsonReceivedChronologicalRosterWindow
end
