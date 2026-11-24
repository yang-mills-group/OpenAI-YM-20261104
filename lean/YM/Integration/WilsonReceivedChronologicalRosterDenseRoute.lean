import YM.Integration.WilsonReceivedChronologicalRosterRoute

/-! Both held observations on every captured finer grid of one original physical archive. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterDenseRoute
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
    {arity:ℕ}(head:Fin arity)(subjects:Fin arity → ℕ)(D:Fin arity → ℕ)(pt:Fin arity → Chamber)
    (caps:Fin arity → ℝ)
    (rent:∀i,‖WilsonReceivedCanonicalSocketSeed.present D i‖≤caps i)(φ:Test arity)(reserve window wanted pole A travel:ℕ)(budget:ℝ)(η:ℝ)(tube:LinkTube G)
    :Prop:=
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
        ∃source:Catalogue R subjects (K-2+1+1),∃_uv:o ≤ m+1,∃vc:m+1<c,∃ck:c<K-2+1+1,
        R.family.S.scale K-R.family.S.scale m ≤ (travel:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))) ∧
        ∀ᶠ per:ℕ in atTop,∀N:ℕ,∀valid:K ≤ N,
          let j:=K-2
          let live:j+1+1 ≤ N:=ks.le.trans valid
          let fine:f ≤ j+1+1:=((WilsonInvariantActionPosition.arrival R reserve f).1.le.trans ks.ge)
          let δ:ℝ:=1
          let rate:=(Real.sqrt (R.family.path.β N per (m+1)))^δ*B^n
          let oldDay:=resident N (old.trans ((Nat.le_succ m).trans (walk.trans
            ((Nat.le_succ j).trans ((Nat.le_succ (j+1)).trans live)))))
          let g:=Pert.Asymptotics.regulatorRun R.family N per
        ∃classroom:Purchased (per:=per) (V:=V) (draw:=draw) (rate:=rate) (allowance:=δ) power P book oldDay κ pt (j+1+1) m live
          (fun j=>base B caps power (L.clock.hatBeta (j+1))) old φ caps A target η,
        WilsonReceivedChronologicalRosterArchivedEdge.Field (R:=R) (V:=V) (draw:=draw)
          power P book resident (fun N per=>(Real.sqrt (R.family.path.β N per (m+1)))^δ*B^n) δ
          (WilsonReceivedCanonicalSocketSeed.present D) κ pt (fun t=>base B caps power (L.clock.hatBeta (t+1))) old walk φ caps A target η
          rent fine live classroom source ∧
          ∀{grid:ℕ}(retest:grid ≤ j+1+1)(site:Fin n → Site (R.family.side grid per)),
            (∀i,WilsonReceivedChronologicalMaterialSites.physical R
              (WilsonReceivedChronologicalMaterialCapture.placed R retest site) ck.le i=0) → 
            ∀{entry grade time:ℕ}{start:entry ≤ j+1+1}
              (panel:WilsonMeasuredPublicEntrancePanel.Panel R k N per entry (j+1+1) start live grade pole time budget)
              (file:WilsonMovingForkHeterogeneousCut.Filed R k (j+1+1)),
              panel.slot=file.station → panel.axis=file.A N per → ∀mask:(Stock.census (Fin n)).Mode,
              let votes:=WilsonOriginalObservedRoseCorrectedWords.votes R k (N:=N) (per:=per) file panel.names panel.turn
              let word:=WilsonIndependentConditionedDenseFilmBank.upper R k (N:=N) retest site votes mask
              let normalized:=WilsonIndependentConditionedDenseFilmTerminal.output (R:=R) (d:=k) (P:=P)
                (N:=N) (j:=j) (per:=per) (first:=m) (V:=V) (draw:=draw) (lens:=D) (pt:=pt)
                (fine:=retest) (site:=site) (votes:=votes) (mask:=mask) c requested
              let wallet:=WilsonReceivedCanonicalVersePortfolio.wallet R k (fun _=>budget) mask.val*
                L.clock.hatBeta (j+1+1)^(pole*mask.val.card)
              (∑q:WilsonReceivedCanonicalVersePortfolio.Selection R k mask.val,
                ‖WilsonReceivedCanonicalVersePortfolio.weight R k N per (j+1+1) votes mask.val q‖) ≤ wallet ∧
              ‖actualTransport R.family (N:=N) word
                ((old.trans (Nat.le_succ m)).trans (vc.le.trans ck.le)) 1-normalized‖ ≤ g (m+1)^wanted ∧
              ‖actualTransport R.family (N:=N) word (vc.le.trans ck.le) 1-normalized‖ ≤ g (m+1)^wanted

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (paths:FundedOriginalVacuumPaths.prices R.kit)
    {arity:ℕ}(head:Fin arity)(subjects:Fin arity → ℕ)(adult:∀i,0<subjects i)(D:Fin arity → ℕ)(pt:Fin arity → Chamber)
    (caps:Fin arity → ℝ)(nonneg:∀v,0 ≤ caps v)(hk:∀v,subjects v < D v)
    (rent:∀i,‖WilsonReceivedCanonicalSocketSeed.present D i‖≤caps i)(φ:Test arity)(reserve window wanted pole:ℕ)(budget:ℝ)(bp:0≤budget)(slow:WilsonWindowReportingPace.Slow R.kit)(tol η:ℝ)(tp:0 < tol)(ep:0 < η)(school:ℕ)(tube:LinkTube G)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (pieces physical:ℕ)(p:Bool → ℕ)(span:U → ℕ)(lag:U → Bool → ℕ):
    ∃A travel:ℕ, Admitted paid paths head subjects D pt caps rent φ reserve window wanted pole A travel budget η tube :=by
  classical
  obtain ⟨A,travel,course⟩:=WilsonReceivedChronologicalRosterCertified.original paid paths head subjects adult
    D pt caps nonneg hk rent φ reserve window wanted pole budget 100 bp slow tol η tp ep school tube ready pieces physical p span lag
  refine ⟨A,travel,?_⟩
  unfold Admitted
  intro refund requested depth n front k κ power target P menu ask L clock0
  obtain ⟨book,price,B,one,release⟩:=course
  refine ⟨book,price,B,one,?_⟩
  filter_upwards [release] with o here
  obtain ⟨warm,opening,resident,quiet,anchor⟩:=here
  refine ⟨warm,opening,resident,quiet,?_⟩
  filter_upwards [anchor] with station commissioned
  obtain ⟨V,draw,metal,pin,uses⟩:=commissioned
  refine ⟨V,draw,metal,pin,?_⟩
  intro program stage band v
  obtain ⟨floor,opened⟩:=uses program stage band v
  refine ⟨floor,?_⟩
  intro t f c late cf pos vc mesh width K m
  obtain ⟨old,walk,ks,source,uv,apart,ears,gate,big,clocked,extent,prices,records⟩:=
    opened t f late cf pos vc mesh width
  have fk:f ≤ K:= (WilsonInvariantActionPosition.arrival R reserve f).1.le
  have born:c<K-2+1+1:=by omega
  have young:c<K-2+1+1-1:=by omega
  refine ⟨old,walk,ks,source,uv,apart,born,extent,?_⟩
  filter_upwards [records] with per repayments
  intro N valid j live fine δ rate oldDay g
  obtain ⟨⟨quote,money,amount,_,cold,_,high,cap,low,atV⟩,hired,priced⟩:=repayments N valid
  obtain ⟨Z,paidQuiet⟩:=quiet N (old.trans ((Nat.le_succ m).trans (walk.trans
    ((Nat.le_succ j).trans ((Nat.le_succ (j+1)).trans live)))))
  have aperture:R.family.S.scale (j+1+1)-R.family.S.scale m ≤ (travel:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))):=by
    rw [show j+1+1=K from ks]
    exact extent
  obtain ⟨pupil,archive,_,_,assay,teacher,pupilAt,sparse,period,current,gridCost,_⟩:=hired
  refine ⟨pupil,archive,?_⟩
  intro grid retest site captured entry grade time start panel file stations axes mask votes word normalized wallet
  let toll:=fun t=>base B caps power (L.clock.hatBeta (t+1))
  have size:0<n:=Nat.zero_lt_of_lt front.isLt
  have strip:(R.family.path.rep N per c).p.supportExponent ≤ 100:=by
    have law:(R.family.path.rep N per c).p=R.family.path.levels.budget c:=
      (R.makes.wilson.represents N per c (born.le.trans live)).vac
    rw [law,paid.support]
  let frontOf(t:Multi.Hot (Stock.census (Fin n))):Fin n:=(show t.val.val.Nonempty from t.property).choose
  have member(t:Multi.Hot (Stock.census (Fin n))):frontOf t∈t.val.val:=
    (show t.val.val.Nonempty from t.property).choose_spec
  exact WilsonReceivedChronologicalRosterSettled.original R simple k P book oldDay old (by omega) live D pt
    toll pupil retest site panel file stations axes mask rent size adult (fun _ _ _=>0) wanted (priced pupil)
    apart born captured young big gate clocked (@quote) money (by norm_num:δ ≤ 1) amount high cap strip
    (ears per).1 (ears per).2 (WilsonReceivedChronologicalFixedRoseGridStock.trees R per)
    (WilsonReceivedChronologicalFixedRoseGridStock.tags R per) (R.family.localSection 0) R.family.params
    paidQuiet tube frontOf member teacher pupilAt sparse period (by omega) (2*A) tol tp ep current gridCost
    paid.support cold low (fun a=>(rent a).trans (atV a)) rfl assay travel
    (by simpa only [Nat.add_sub_cancel] using aperture) prices

end YM.Integration.WilsonReceivedChronologicalRosterDenseRoute
end
