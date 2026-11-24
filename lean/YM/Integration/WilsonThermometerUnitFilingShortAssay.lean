import YM.Integration.WilsonThermometerUnitFilingEarnedAssay
import YM.Integration.WilsonThermometerUnitFilingArmInvoice
import YM.Integration.WilsonThermometerUnitFilingPupilClock

/-! The fixed hearing and the moving perturbative return of the same full signed thermal source. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingShortAssay
open RG16 RG16.Literal Trace.Physical.GermGraph
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonLimitConstruction WilsonOriginalStarSceneRent WilsonOriginalThermometerMicroscopic
open WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators

open OPE.Therm Pert.Asymptotics WilsonReceivedFirstTrace WilsonPositionThermometerGradedSource WilsonThermometerCourseHearing

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m t N per k:ℕ}
  (top:t<N) (o:Positions (Fin 3) (R.family.side N per))
local notation "faces" itr:max => WilsonThermometerCourseHearing.offered R A simple itr o
local notation "arr" j:max jt:max => WilsonReceivedCloseHistory.history (N:=N) R WilsonThermometerCourseHearing.disks (faces top) j jt

variable (hk:Burn.horizon k+2≤R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (tab:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
  {φ:ℕ→ℕ} (books:Mentor.Offices.Books D R.rolls tab φ) (ahead:Mentor.Forecast D R.rolls tab φ books)
  (order shelf seats:ℕ)
local notation "ages" => (fun v:Fin 3=>(grade v).val)
local notation "post" j:max mj:max y:max => WilsonOriginalReceivedChain.Post (N:=N) R hk D tab π Γ Ψ books
  ahead WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors ages order shelf seats j mj y
variable (W:Registration (m:=m) (N:=N) (k:=k) R D tab π Γ Ψ books ahead WilsonThermometerCourseHearing.disks shelf seats)
  (mt:m≤t)
local notation "B" => budgetR R
local notation "roof" j:max => ∏ l∈Ico j t,(B l)^2*(B (l+1))^7
local notation "g" => regulatorRun R.family N per

open WilsonThermometerAncestralTrace WilsonThermometerCenteredAlgebra
local notation "headroom" mj:max L:max => Oak.expenseReal R hk D tab π Γ books mj
  (L).op (L).lesson ahead order shelf

open WilsonThermometerWeightedCapture WilsonFiniteOrdinaryInverse WilsonThermometerCourseIntake
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order
open Planned.GuardedAtom Push.Local WilsonMeasuredCoefficientTransport
open WilsonPhysicalMarkedDefect.RegularProjection
local notation "stencil" => R.family.params
local notation "field₀" => R.family.labels.level 0
local notation "section₀" => R.family.localSection 0
local notation "J₃" => Stock.census (Fin 3)
local notation "strip" => (∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
  Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
local notation "stage₀" α:max => WilsonFullFaceSignedPower.constants section₀ stencil α ((2:ℝ)^(order+shelf+2)+4)
local notation "unit₀" => |testPrice field₀ * fee J₃ * WilsonFullFaceSignedPower.inter *
      (Fintype.card (Multi.parts (J₃)).Mode:ℝ)*125|
local notation "lamps" i:max mi:max L:max => rendered
  (Oak.student (n:=per) R hk D tab π Γ books mi (L).op (L).lesson ahead WilsonThermometerCourseHearing.disks
    (L).model order (L).voter) (Ψ i).p (Coat.gStep (Ψ (i+1)).beta)
local notation "ordinary" L:max => fun v=>((L).model v).paint WilsonThermometerCourseHearing.fired
local notation "roster" i:max L:max => Air.craft (L).model (ordinary L) ages
  (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
local notation "sheet" i:max => R.family.path.levels.clock.op i per
local notation "homes" i:max L:max => ((L).passport.coarser (sheet i).ratio).origin
local notation "base" i:max => Stationary.arm G (R.family.side i per) 1
local notation "budget₀" i:max => R.family.path.levels.budget i
local notation "topPost" i:max live:max => (RunFormalChain.fromRun R).step N i per live
local notation "canon" i:max => R.family.path.rep N per i
local notation "κ" i:max => LocalComparison.forcedDivisor R.family i

open RG12 XSpace WilsonThermometerAlignedCells
open Primitives.GCC.Anchor

variable (r:ℝ) (profile:Test 3)
local notation "Grid" => WilsonThermometerSupportedCells.Occupied (N:=N) (per:=per) R r profile
local notation "home₀" c:max => WilsonThermometerRegisteredCells.placement (R:=R) (N,per) (c).val
local notation "offer₀" u:max c:max => WilsonThermometerCourseHearing.offered R A simple u (home₀ c)
local notation "weight₀" c:max => mass (R:=R) r (N,per) profile (c).val
local notation "material₀" n:max live:max L:max a:max => Order.value (g (n+1):ℂ) (Order.ratio
  (PhysicalWilsonPeriodizedMaterial.reference R N n per live ((base n) a) (roster n L) order))
local notation "original₀" live:max c:max U:max Q:max =>
  (total (incoming R A simple (Nat.le_of_lt live) (home₀ c) U) Q).part full
local notation "filed₀" n:max mj:max L:max U:max Q:max =>
  (total (Poly.pass (WilsonRootedKioskOccupiedSlip.bare (lamps n mj L) WilsonThermometerCourseHearing.fired U)) Q).part full
local notation "variation₀" => ∫x:Points 3,‖profile x‖

open Function Filter MeasureTheory Extraction Lattice Wilson Labels RG Source Extra.Histories
open Push Marker Extra.Multi PhysicalNext.Repeat.Legato MergeProof Accent
open Bid Bandage Cells Stock RG16.Literal Trace.Physical.GermGraph GridApprox
open Motion Menu Ribbons Ribbons.ManyCopies Next.Rank Ribbon Trace.Physical
open RG05Readout Native Address Many Records Harvest Copper PhysMS
open WilsonReflectedMicroscopicSites WilsonReflectedPhysicalRate OPE OPE.Log Trace.Pilot
open WilsonPositionThermometerCapStation WilsonThermometerCourseIntake
open WilsonPositionThermometerGradedSource (grade)
open WilsonPositionThermometerGradedReading (vector)
open WilsonCapturedPrimaryFaceWallet WilsonCapturedPrimaryActiveArms
open OPE.Cards XSpace XSpace.Normalize XSpace.Rose
open Table Spec Climb Next.UVStress RG12 RG17
open WilsonCapturedPrimaryStationArms (nominees)
open WilsonThermometerAlignedCells (placedAt atOrigin mass)
open Next.UVStress OPE.Cards
open Finset Function Matrix Lattice Wilson RG RG.Supply Precision Tree Exterior Laurent Bloch
open Marker Multi PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants Next.Rank Next.SectorChange WilsonCoeffUV FreeResolvent MeasureTheory

private theorem comparison {x old younger:ℂ} {face localFee native paid tail:ℝ}
    (input:‖x-old‖  ≤  face+(native+localFee)) (stop:‖old-younger‖ ≤ tail) (width:native ≤ paid):
    ‖x-younger‖  ≤  face+(paid+localFee+tail):=by
  calc ‖x-younger‖ = ‖(x-old)+(old-younger)‖:=by congr 1;abel
    _ ≤ _:=norm_add_le _ _
    _ ≤ _:=add_le_add input stop
    _ ≤ _:=by linarith only [width]

theorem original (inlet:∀u:Grid,post t mt (offer₀ top u)) (counted:∀u,Countable (inlet u).inputIndex)
    (refs:∀v:Fin 3,R.family.ref (grade v)  ≤  N)
    (path:PlanV.Path D R.alloy tab (Burn.horizon k) N m π Γ)
    (ticket:TicketP R.alloy R.kit D tab) (month:Scholar.Month R.rolls D tab R.alloy.delay)
    (fits:order  ≤  Burn.horizon k+1) (packed:order+shelf  ≤  Burn.horizon k+2)
    (q l degree:ℕ) {price:ℝ} (cap:0  ≤  price) (deep:2*(q+2)+8  ≤  order) (aged:q+2+3  ≤  3*k+2) {i:ℕ}
    (late:WilsonReceivedMeasuredStampPrice.opening R W.simple (q+2) order k deep aged zero_lt_one  ≤  i+1)
    (weak:(eventually_atTop.mp (WilsonThermometerAncestralCalendar.weak R simple)).choose  ≤  i)
    (mi:m  ≤  i) (both:i+2  ≤  t) {u : ℕ} (floor : m  ≤  u) (ui : u  ≤  i)
    (gate:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ))  ≤  u)
    (days:((t-i:ℕ):ℝ)  ≤  price*(Real.log (2+Real.log (R.alloy.B.a.clock.hatBeta i)))^degree)
    (booked:(eventually_atTop.mp (WilsonThermometerAncestralFunds.original R simple (degree+1) seats q l cap)).choose  ≤  i)
    (oldRent:∀u,(inlet u).rent  ≤  (g t)^(q+2)) (start:∀u,(g t)^l  ≤  Poly.toll (inlet u).w full) 
    (way:WayStation R.kit) (station:WilsonCenteredCaptureClock.first R simple  ≤  i) (sec:R.t 0  ≤  i)
    (slow:∀ j,((R.family.S.block j).val:ℝ)  ≤  Real.log (RG16.Lambda R.family.path.levels j))
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (early:(eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose  ≤  i)
    (activated:(eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose  ≤  i)
    (force:q  ≤  R.alloy.B.a.clock.J i)
    (opening:∀c  ≤  seats, WilsonFirstReceivedEarnedFee.opening R simple c q order k (by omega) (by omega)
      (show (0:ℝ)<1/4 by norm_num)  ≤  i)
    (saved:(eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple q)).choose  ≤  i)
    (stripGrant:strip) (depth:ℕ) (H cap₀:ℝ) (hc:0  ≤  cap₀) (fit:k  ≤  R.alloy.B.a.clock.J i)
    (heard:(eventually_atTop.mp (WilsonThermometerCenteredCompensation.original R simple D φ stripGrant order shelf
      k seats depth H cap₀ hc)).choose  ≤  i)
    (fund:Volume.Fund D R.rolls tab φ books R.alloy.delay) (target:ℕ) (surplus:target+(3+(l+2)+87)  ≤  q)
    (born:∀u v,(inlet u).passport.origin v=(R.family.S.toDepth top per).parent ((home₀ u).origin v))
    (room:(eventually_atTop.mp (WilsonThermometerRegisteredTripleRoom.spatial R simple profile)).choose  ≤  i)
    (space:|r|  ≤  R.family.S.a i) (support:(R.family.path.levels.budget i).supportExponent  ≤  100)
    (a:Grid → Stationary.Link G (R.family.side i per)) (z:Grid → ℝ)
    (allow:∀u,|z u|  ≤  |H| * (Real.log (R.family.path.levels.clock.hatBeta i))^depth*
      (((budget₀ i).B:ℝ)^2*(budget₀ i).threshold)/(g (i+1)))
    (inside:∀u e,‖Exterior.collect G ((base i) (a u)) e‖  ≤  cap₀*|z u|)
    {J:ℕ} {K:ℝ} (S:WilsonThermometerUnitFilingReflectionBank.Bank R N per u J r K profile)
    {f:Extraction.Order} {Θ:(Bel R.family.book).Hierarchy} (checked:A.station.checked f Θ A.horizon)
    (unit:∀ t:Fin 7,A.change t ((Bel R.family.book).unit t)=(Bel R.family.book).unit t)
    (before:A.station.k<N)
    (qual:WilsonThermometerUnitFilingShapeReceived.Qualified R A simple (N,per))
    (door:Opened R.family 0 u per) (kn:0 ≤ K) (rn:0 ≤ r)
    (calendar:WilsonThermometerUnitFilingPupilClock.start R simple slow u (l+2) target  ≤  i)
    (opened:Opened R.family 0 (WilsonThermometerUnitFilingPupilClock.date R simple slow u (l+2) target i calendar) per) :
    let live:i<N:=by omega
    let g₀:=g (i+1)
    let expense:=|fee J₃*stage₀ 100| * (4^q+2)*g₀^target
    ∃(L:∀u:Grid,post i mi (offer₀ live u)) (Q:Grid → Poly J₃),
    (∀u:Grid,Reached R simple A top (home₀ u) hk D tab π Γ Ψ books ahead order shelf seats W mt (inlet u)
      (counted u) (q+2) 1 mi (show i  ≤  t by omega) (L u) ∧
      (∀v,(homes i (L u)) v=(R.family.S.toDepth live.le per).parent ((home₀ u).origin v)) ∧
      g₀^(l+2)  ≤  Poly.toll (L u).w full ∧ Q u=material₀ i live (L u) (a u) ∧
      (∀(f:Forest (sheet i).ratio) (v:(sheet i).Choices),
        Order.value (g₀:ℂ) (Order.ratio (Bulk.Fk (topPost i live) f v (roster i (L u)) ((base i) (a u)) order))=Q u) ∧
      Poly.price (fun v=>g₀*(L u).w v) (inverseMass (Q u))  ≤  fee J₃) ∧
    let filed:=fun U=>∑u:Grid,weight₀ u*filed₀ i mi (L u) U (Q u)
    let Y:=WilsonThermometerUnitFilingRelative.source R A (N,per) r profile Q
    let v:=WilsonThermometerUnitFilingPupilClock.date R simple slow u (l+2) target i calendar
    let vi:=(WilsonThermometerUnitFilingPupilClock.range R simple slow u (l+2) target i calendar).2.1.le
    let earlier:=WilsonThermometerUnitFilingCoarse.reading R (N:=N) (fun U=>((canon i).eval U:ℂ)*filed U) v vi
    let observed:=WilsonThermometerUnitFilingCylinder.tested R A (N,per) r profile
      (WilsonThermometerUnitFilingRelative.table R (N,per) r profile Q)
    let E:=variation₀*(fee J₃*WilsonPlantedOrdinaryHalo.master section₀ stencil 100 ((2:ℝ)^(order+shelf+2)))
    ∀(y:WilsonThermometerUnitFilingReflectionBank.lifts (N:=N) (p:=per) R r profile),
      WilsonThermometerUnitFilingReflectionBank.Primary R S A y →
    ∀ M:ℝ,0 ≤ M→(∀ c:Grid,∀ α:(J₃).Mode,
      Poly.toll (L c).w α * WilsonThermometerUnitFilingArmInvoice.seats R y c α ≤ M) →
    let spatial:=((variation₀*(fee J₃/g₀^(3+(l+2)))*M)*(K*r^(1/32:ℝ)))
    let bound:=spatial+variation₀*(unit₀*g₀^target+5*expense)+40*(2*E+1)*g₀^target
    PaidAt R.family.S N per J (R.family.beta N per) (WilsonThermometerUnitFilingRelativeStation.rent R r K profile Q y)
      (Y-WilsonThermometerUnitFilingFeed.report R Y u • (1:Cut R.family N per)) ∧
    ‖observed-earlier‖ ≤ bound ∧
    let residual:=fun (c:Grid)=>WilsonThermometerCenteredScalar.read (total
      (WilsonThermometerUnitFilingRelativeCells.measured R A (N,per) r profile c) (Q c))
    ∀ A₂ A₁ A₃:ℝ,0 ≤ A₂→0 ≤ A₁→
    (∀s:Finset (Fin 3),s.card=2→∑c:Grid,‖weight₀ c‖*‖residual c s‖^2 ≤ A₂^2)→
    (∀j:Fin 3,∑c:Grid,‖weight₀ c‖*‖residual c {j}‖^2 ≤ A₁^2)→
    (∀j:Fin 3,∑c:Grid,‖weight₀ c‖*‖residual c {j}‖^3 ≤ A₃^3)→
    ‖profile.applyTo (WilsonPositionThermometerGradedReading.full r A (N,per))-
      WilsonThermometerUnitFilingRelativeCells.reference R (N,per) r profile Q-earlier‖ ≤ 
      (3*(A₂*A₁)+2*A₃^3)+bound:=by
  classical
  intro live g₀ expense
  obtain ⟨L,Q,bank,hearing⟩:=WilsonThermometerUnitFilingEarnedAssay.original R simple A top hk D tab π Γ Ψ books ahead order shelf seats
    W mt r profile inlet counted refs path ticket month fits packed q l degree cap deep aged late weak mi both floor ui gate
    days booked oldRent start way station sec slow ready early activated force opening saved stripGrant depth H cap₀ hc fit
    heard fund target surplus born room space support a z allow inside S checked unit before qual door
  refine ⟨L,Q,bank,?_⟩
  intro filed Y v vi earlier observed E y hit M mp earned spatial bound
  let old₀:=WilsonThermometerUnitFilingCoarse.reading R (N:=N) (fun U=>((canon i).eval U:ℂ)*filed U) u ui
  obtain ⟨paid,source,connected⟩:=hearing y hit
  have gp:=((eventually_atTop.mp (WilsonThermometerAncestralCalendar.weak R simple)).choose_spec i weak N per
    (i+1) (Nat.le_succ i) live)
  have restored:=WilsonThermometerUnitFilingArmInvoice.original R r K profile Q y (fun c=>(L c).w) gp.1 gp.2 kn rn
    (l+2) (fun c=>(L c).salary.positive) (fun c=>(bank c).2.2.1) (fun c=>(bank c).2.2.2.2.2) mp earned
  have stop:=WilsonThermometerUnitFilingPupilClock.original R simple A hk D tab π Γ Ψ books ahead order shelf seats
    r profile live mi W.course L Q (fun c=>(bank c).2.1) (l+2) (fun c=>(bank c).2.2.1)
    (fun c=>(bank c).2.2.2.2.2) door.post ui door sec station slow ready early activated ticket.1 W.hospital
    (W.narrow.trans (R.alloy.B.a.fits.mono mi)) W.load weak room target calendar opened space support
  let native:=WilsonThermometerUnitFilingRelativeStation.rent R r K profile Q y
  let localFee:=variation₀*(unit₀*g₀^target+5*expense)
  let tail:=40*(2*E+1)*g₀^target
  have sourcePrice:‖observed-old₀‖  ≤  native+localFee:=source
  have transport:‖old₀-earlier‖ ≤ tail:=stop
  have arm:native ≤ spatial:=restored
  have head:‖observed-earlier‖ ≤ bound:=by
    simpa only [zero_add] using @comparison observed old₀ earlier 0 localFee native spatial tail
      (by rw [zero_add];exact sourcePrice) transport arm
  refine ⟨paid,head,?_⟩
  intro residual a₂ a₁ a₃ h₂ h₁ two one three
  let joined:=profile.applyTo (WilsonPositionThermometerGradedReading.full r A (N,per))-
      WilsonThermometerUnitFilingRelativeCells.reference R (N,per) r profile Q
  have fixed:=connected a₂ a₁ a₃ h₂ h₁ two one three
  exact @comparison joined old₀ earlier (3*(a₂*a₁)+2*a₃^3) localFee native spatial tail fixed transport arm

end YM.Integration.WilsonThermometerUnitFilingShortAssay
