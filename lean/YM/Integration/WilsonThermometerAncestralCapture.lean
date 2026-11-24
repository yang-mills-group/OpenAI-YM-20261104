import YM.Integration.WilsonThermometerAncestralAppointment
import YM.Integration.WilsonThermometerAncestralHomes
import YM.Integration.WilsonThermometerAncestralCell
import YM.Integration.WilsonMeasuredSignedScalar
import YM.Integration.WilsonThermometerAncestralCalendar

/-! Price the single marked gallery along the original two nonbare post operations
and the booked close interval preceding them. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerAncestralCapture
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

theorem original (inlet:post t mt (faces top)) (counted:Countable inlet.inputIndex)
    (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N)
    (path:PlanV.Path D R.alloy tab (Burn.horizon k) N m π Γ)
    (pass:Pass D tab R.alloy R.kit) (month:Scholar.Month R.rolls D tab R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1) (packed:order+shelf ≤ Burn.horizon k+2)
    (q l degree:ℕ) {price:ℝ} (cap:0 ≤ price) (deep:2*(q+2)+8 ≤ order) (aged:q+2+3 ≤ 3*k+2) {i:ℕ}
    (late:WilsonReceivedMeasuredStampPrice.opening R W.simple (q+2) order k deep aged zero_lt_one ≤ i+1)
    (weak:(eventually_atTop.mp (WilsonThermometerAncestralCalendar.weak R simple)).choose ≤ i)
    (mi:m ≤ i) (both:i+2 ≤ t)
    (days:((t-i:ℕ):ℝ) ≤ price*(Real.log (2+Real.log (R.alloy.B.a.clock.hatBeta i)))^degree)
    (booked:(eventually_atTop.mp (WilsonThermometerAncestralFunds.original R simple (degree+1) seats q l cap)).choose ≤ i)
    (oldRent:inlet.rent ≤ (g t)^(q+2)) (start:(g t)^l ≤ Poly.toll inlet.w full) 
    (way:WayStation R.kit) (station:WilsonCenteredCaptureClock.first R simple ≤ i) (sec:R.t 0 ≤ i)
    (slow:∀ j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (early:(eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (activated:(eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (force:q ≤ R.alloy.B.a.clock.J i)
    (opening:∀c ≤ seats, WilsonFirstReceivedEarnedFee.opening R simple c q order k (by omega) (by omega)
      (show (0:ℝ)<1/4 by norm_num) ≤ i)
    (saved:(eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple q)).choose ≤ i)
    (stripGrant:strip) (depth:ℕ) (H cap₀:ℝ) (hc:0 ≤ cap₀) (fit:k ≤ R.alloy.B.a.clock.J i)
    (heard:(eventually_atTop.mp (WilsonThermometerCenteredCompensation.original R simple D φ stripGrant order shelf
      k seats depth H cap₀ hc)).choose ≤ i)
    (fund:Volume.Fund D R.rolls tab φ books R.alloy.delay) (target:ℕ) (surplus:target+(3+(l+2)+87) ≤ q)
    (born:∀v,inlet.passport.origin v=(R.family.S.toDepth top per).parent (o.origin v))
    (profile:Test 3) (r:ℝ) (room:(eventually_atTop.mp (WilsonThermometerRegisteredTripleRoom.spatial R simple profile)).choose ≤ i)
    (space:|r| ≤ R.family.S.a i) (relative:Site (R.family.side N per) × Site (R.family.side N per))
    (placed:o.origin=atOrigin relative) (massAt:mass (R:=R) r (N,per) profile relative≠0)
    (support:(R.family.path.levels.budget i).supportExponent ≤ 100) :
    let live:i<N:=by omega
    let y₀:=g (i+1)
    ∃L:post i mi (faces live), Reached R simple A top o hk D tab π Γ Ψ books ahead order shelf
      seats W mt inlet counted (q+2) 1 mi (show i ≤ t by omega) L ∧
    (∀v,(homes i L) v=(R.family.S.toDepth live.le per).parent (o.origin v)) ∧
    ∀(a:Stationary.Link G (R.family.side i per)) (z:ℝ),
      |z| ≤ |H| * (Real.log (R.family.path.levels.clock.hatBeta i))^depth*
        (((budget₀ i).B:ℝ)^2*(budget₀ i).threshold)/y₀ →
      (∀e,‖Exterior.collect G ((base i) a) e‖ ≤ cap₀*|z|) →
    let Q:=Order.value (y₀:ℂ) (Order.ratio (PhysicalWilsonPeriodizedMaterial.reference R N i per live ((base i) a) (roster i L) order))
    (∀(f:Forest (sheet i).ratio) (v:(sheet i).Choices),
      Order.value (y₀:ℂ) (Order.ratio (Bulk.Fk (topPost i live) f v (roster i L) ((base i) a) order))=Q) ∧
    let prior:=fun U=>(total (incoming R A simple (Nat.le_of_lt live) o U) Q).part full
    let filed:=fun U=>(total (Poly.pass (WilsonRootedKioskOccupiedSlip.bare (lamps i mi L)
      WilsonThermometerCourseHearing.fired U)) Q).part full
    let expense:=|fee J₃*stage₀ 100| * (4^q+2)*y₀^target
    ∃h:Coefficient field₀ (R.family.side i per),h.Format 0 stencil (Ψ i) ∧ h.remBound 0 (Ψ i) (κ i) expense ∧
      (field₀).coeffSize h.x ≤ unit₀ * y₀^target ∧
      (∀U,h.density 0 section₀ (Ψ i) U=prior U-((Ψ i).eval U:ℂ)*filed U) ∧
      WilsonThermometerCompulsoryReturn.Heard R (top:=N)
        (fun U=>prior U/((Ψ i).eval U:ℂ)-filed U-account h (Ψ i) U/((Ψ i).eval U:ℂ)) (‖h.x 0‖+expense) ∧
      (∀U,h.density 0 section₀ (Ψ i) U-(soft h).density 0 section₀ (canon i) U=account h (Ψ i) U) ∧
      ∀U,account h (Ψ i) U≠0 → ∃j,h.forced j U≠0 ∧ 0∈((canon i).activities.forced j).support ∧
        ∃z,z∈((canon i).activities.forced j).inventory ∧ z∈flags (canon i).p.threshold U := by
  intro live y₀
  obtain ⟨L,trace,chart⟩:=WilsonThermometerAncestralAppointment.original R simple A top o hk D tab π Γ Ψ
    books ahead order shelf seats W mt inlet counted refs path pass month fits packed q l degree cap deep
    aged late weak mi both days booked oldRent start way station sec slow ready early activated force opening saved
    stripGrant depth H cap₀ hc fit heard fund target surplus
  have it:i ≤ t:=by omega
  have homesAt:=WilsonThermometerAncestralHomes.placed R simple A top o hk D tab π Γ Ψ books ahead
    order shelf seats W mt inlet counted q refs born mi it L trace
  obtain ⟨center,locations,distance⟩:=WilsonThermometerAncestralHomes.original R simple A top o hk D tab
    π Γ Ψ books ahead order shelf seats W mt inlet counted q refs born mi it L trace profile r room space relative
    placed massAt
  have strength:(Ψ i).p.supportExponent ≤ 100 := by
    rw [(W.course.1.walk i mi live.le).truep.point];exact support
  exact ⟨L,trace,homesAt,chart 0 (halo (Ψ i).p.B {0}) center locations (Ψ i).p.B distance le_rfl
    (by rfl) 100 strength⟩

end YM.Integration.WilsonThermometerAncestralCapture
