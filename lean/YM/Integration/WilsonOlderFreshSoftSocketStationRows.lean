import YM.Integration.WilsonOlderFreshSoftSocketStationBerth
import YM.Integration.WilsonOlderFreshSoftSocketTrueNorm

/-! Price the complete normalized K-planted ordinary field on its indicated physical roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationRows
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


open WilsonOlderFreshSoftSocketStationSale (rent covers)
open WilsonOlderFreshSoftSocketStationStops (ticket money Paired depth)
open WilsonOlderFreshSoftSocketStationTerminal (invoice)
variable {ord:Extraction.Order}{hier:(Bel R.family.book).Hierarchy}
theorem same (D:Fin 3→ℕ)(p:ℕ)(V V₁:Realm G (p+1) Credit.leanC)(draw:V.draws=R.family.path.levels)
    (hub:V₁.draws=R.family.path.levels)(scheme:V.paid=R.metals.O)(scheme₁:V₁.paid=R.metals.O)
    (N per K c w v:ℕ)(stem:c≤N)(y:Sites N per×Sites N per)(t:Faces)(trial:TestAt D t)(g:ℝ)
    (x:∀i,(R.family.labels.level (grade i)).Coeff)(j:ℕ)(θ:ℝ)(early:Bool):
    row (R:=R) D V t N K c w v (enrolled R D V draw N per c stem y t trial) g x j θ early=
      row (R:=R) D V₁ t N K c w v (enrolled R D V₁ hub N per c stem y t trial) g x j θ early:=by
  let d:=grade ∘ seat t
  let root:=fun i:t=>WilsonOriginalPublicFixedCourse.home R per c stem (atOrigin y) (WilsonOlderFreshSoftRoseNodes.anchor t) (seat t i)
  let tape:Digits R.family.path.levels t:=fun l i=>WilsonOriginalPublicFixedCourse.digits R per (atOrigin y) l (seat t i)
  let arm (L:Levels G)(O:ChartRatio G)(cells:Digits L t):ℂ:=
    let P:=WilsonOlderFreshSoftTrialCut.source R (D ∘ seat t) d N K c L O trial.coeff trial.phase cells root univ trial.test
    let h:=mass d (univ:Finset t)
    if early then WilsonOlderFreshSoftCoveredRead.cost R d L O N w v j θ g (fun i=>x (seat t i)) (fun b=>cruises L O N h c w (P b))
    else WilsonOlderFreshSoftFigureReading.reading R d g (fun i=>x (seat t i)) (fun b=>cruises L O N h c v (P b)) j θ
  have cofile {L:Levels G}{O:ChartRatio G}(h:L=R.family.path.levels)(out:O=R.metals.O):
      arm L O (h.symm ▸ tape)=arm R.family.path.levels R.metals.O tape:=by
    cases h;cases out;rfl
  exact (cofile draw scheme).trans (cofile hub scheme₁).symm

def Compared (D:Fin 3→ℕ)(p q:ℕ)(C:Fin 3→ℝ)(η:ℝ)
    (A₀:Group R.family 6)(r:ℝ)(order:ℕ)(M:Fin 3→ℝ)(reg:Indexed R grade (fun _=>A₀.station.k) order η M (filed R A₀))
    (v N per K c w:ℕ)(V:Realm G (p+1) Credit.leanC)(draw:V.draws=R.family.path.levels)
    (kK:A₀.station.k≤K)(ck:c≤K)(live:K<N):Prop:=
  ∀(j:ℕ),j≤p→∀(θ:ℝ),|θ|≤1→∀(t:Faces),t.Nonempty→∀(y:Sites N per×Sites N per)(trial:TestAt D t),
    let a:=enrolled R D V draw N per c (ck.trans live.le) y t trial
    let g:=regulatorRun R.family N per K
    let x:=vector R grade (fun _=>A₀.station.k) K order η M (filed R A₀) (fun _=>kK) reg N per
    let pay:=fun i=>(r/R.family.S.a K)^grade i
    ‖scaled t pay (row (R:=R) D V t N K c w v a g x j θ false)-
      scaled t pay (row (R:=R) D V t N K c w v a g x j θ true)‖≤ticket R t C*g^q

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R crop W)
    (D:Fin 3→ℕ)(fit:∀i,grade i<D i)(p q width:ℕ)(opt:ℝ)(opt0:0≤opt){ξ τ δ η:ℝ}
    (xp:0<ξ)(tp:0<τ)(dp:0<δ)(ep:0<η):
    ∀ᶠv:ℕ in atTop,∀(order N per K c w:ℕ)(A₀:Group R.family 6)(_checked:A₀.station.checked ord hier A₀.horizon)(r:ℝ),
    A₀.station.wheel.r=r→v≤A₀.station.k→∀(kK:A₀.station.k≤K),v≤w→w≤c→∀(ck:c≤K)(live:K<N),v+1≤K→
    8≤R.family.path.levels.clock.hatBeta K→
    R.family.S.a A₀.station.k/R.family.S.a K≤R.family.path.levels.clock.hatBeta A₀.station.k^width→
    R.family.S.scale K-R.family.S.scale v≤opt*(1+Real.log (R.family.path.levels.clock.hatBeta (v+1)))→
    ∀(V:Realm G (p+1) Credit.leanC)(draw:V.draws=R.family.path.levels),V.paid=R.metals.O→∀(m C M:Fin 3→ℝ)
      (reg:Indexed R grade (fun _=>A₀.station.k) order η M (filed R A₀)),
      (∀i,0 ≤ m i)→(∀i,0≤C i)→(∀i,0≤M i)→(∀i,M i≤C i*(R.family.path.levels.clock.hatBeta K)^(m i))→
      R.family.S.a c/R.family.S.a w≤Real.exp (-(depth R width ξ η τ δ m q)*Real.log (regulatorRun R.family N per K)⁻¹)→
      Compared R D p q C η A₀ r order M reg v N per K c w V draw kK ck live:=by
  obtain ⟨start,panels⟩:=WilsonOlderFreshSoftRoseMarket.original paid D fit p opt τ opt0 tp
  obtain ⟨age,unit⟩:=eventually_atTop.mp (WilsonOlderFreshSoftSocketStationUnits.original R simple width xp)
  filter_upwards [panels,eventually_ge_atTop start,eventually_ge_atTop age] with v board staffed older
  intro order N per K c w A₀ checked r rr vk kK vw wc ck live away warm planted span V draw scheme m C M reg m0 C0 M0 salary gap
    j keep θ low t occupied y trial probe g x pay
  obtain ⟨V₁,hub,scheme₁,_,_,shelf⟩:=board
  let other:=enrolled R D V₁ hub N per c (ck.trans live.le) y t trial
  let k:=A₀.station.k
  let z:=Real.log g⁻¹
  have rpos:0<r:=rr ▸ A₀.station.wheel.rad
  have pos i:0≤pay i:=pow_nonneg (div_nonneg rpos.le (R.family.S.a_pos _).le) _
  have cash i:M i≤C i*Real.exp ((2*(3*m i/2))*z):=by
    have rate:=WilsonOlderFreshSoftSocketStationScale.heated R N per K live.le warm (m i) (m0 i)
    rw [show 2*(3*m i/2)=3*m i by ring]
    exact (salary i).trans (mul_le_mul_of_nonneg_left rate (C0 i))
  have hold:=unit A₀.station.k (older.trans vk) A₀.station.b checked.high.2 A₀.station.k K N per le_rfl kK live.le warm planted
  have inc i:pay i≤Real.exp ((grade i:ℝ)*(3*((width:ℝ)+ξ))*z):=by
    change (r/R.family.S.a K)^_≤_
    rw [←rr]
    exact hold.2 (grade i)
  have tall:rent R width ξ η m t+τ+(q:ℝ)≤depth R width ξ η τ δ m q/4:=by
    have pre:=WilsonOlderFreshSoftSocketStationSale.covers R width ξ η δ m 0 t
    simp only [Nat.cast_zero,zero_add] at pre
    unfold WilsonOlderFreshSoftSocketStationStops.depth
    linarith only [pre,dp]
  rw [same R D p V V₁ draw hub scheme scheme₁ N per K c w v (ck.trans live.le) y t trial g x j θ false,
    same R D p V V₁ draw hub scheme scheme₁ N per K c w v (ck.trans live.le) y t trial g x j θ true]
  have earn:=WilsonOlderFreshSoftRoseMarket.issued (R:=R) (shelf t occupied) (fun _=>k) (fun _=>staffed.trans vk)
    N per K c w order vw wc ck live away (by linarith only [warm]) span η M (filed R A₀) (fun _=>kK) reg ep.le M0
    pay (fun i=>3*m i/2) C (fun _=>3*(width:ℝ)) (fun _=>3*((width:ℝ)+ξ))
    (depth R width ξ η τ δ m q) q pos C0 cash (fun _=>hold.1) inc gap tall other j keep θ low
  have gpos:=ActualRunKernelPackets.regulator_pos R N per K live.le
  apply earn.trans_eq
  rw [WilsonOlderFreshSoftSocketStationStops.ticket,if_pos occupied]
  have ga:Real.exp (-(q:ℝ)*Real.log g⁻¹)=g^q:=by
    rw [Real.log_inv,neg_mul_neg,Real.exp_nat_mul,Real.exp_log gpos]
  rw [ga]

end YM.Integration.WilsonOlderFreshSoftSocketStationRows
end
