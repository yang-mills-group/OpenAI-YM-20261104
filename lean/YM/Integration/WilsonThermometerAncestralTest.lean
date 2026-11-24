import YM.Integration.WilsonThermometerAncestralCapture
import YM.Integration.WilsonThermometerAncestralLastWallet
import YM.Integration.WilsonThermometerSupportedCells
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerAncestralTest
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

theorem original (inlet:∀u:Grid,post t mt (offer₀ top u)) (counted:∀u,Countable (inlet u).inputIndex)
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
    (oldRent:∀u,(inlet u).rent ≤ (g t)^(q+2)) (start:∀u,(g t)^l ≤ Poly.toll (inlet u).w full) 
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
    (born:∀u v,(inlet u).passport.origin v=(R.family.S.toDepth top per).parent ((home₀ u).origin v))
    (room:(eventually_atTop.mp (WilsonThermometerRegisteredTripleRoom.spatial R simple profile)).choose ≤ i)
    (space:|r| ≤ R.family.S.a i) (support:(R.family.path.levels.budget i).supportExponent ≤ 100)
    (a:Grid → Stationary.Link G (R.family.side i per)) (z:Grid → ℝ)
    (allow:∀u,|z u| ≤ |H| * (Real.log (R.family.path.levels.clock.hatBeta i))^depth*
      (((budget₀ i).B:ℝ)^2*(budget₀ i).threshold)/(g (i+1)))
    (inside:∀u e,‖Exterior.collect G ((base i) (a u)) e‖ ≤ cap₀*|z u|) :
    let live:i<N:=by omega
    let g₀:=g (i+1)
    let expense:=|fee J₃*stage₀ 100| * (4^q+2)*g₀^target
    ∃(L:∀u:Grid,post i mi (offer₀ live u)) (Q:Grid → Poly J₃),
    (∀u:Grid,Reached R simple A top (home₀ u) hk D tab π Γ Ψ books ahead order shelf seats W mt (inlet u)
      (counted u) (q+2) 1 mi (show i ≤ t by omega) (L u) ∧
      (∀v,(homes i (L u)) v=(R.family.S.toDepth live.le per).parent ((home₀ u).origin v)) ∧
      g₀^(l+2) ≤ Poly.toll (L u).w full ∧ Q u=material₀ i live (L u) (a u) ∧
      (∀(f:Forest (sheet i).ratio) (v:(sheet i).Choices),
        Order.value (g₀:ℂ) (Order.ratio (Bulk.Fk (topPost i live) f v (roster i (L u)) ((base i) (a u)) order))=Q u) ∧
      Poly.price (fun v=>g₀*(L u).w v) (inverseMass (Q u)) ≤ fee J₃) ∧
    let prior:=fun U=>∑u:Grid,weight₀ u*original₀ live u U (Q u)
    let filed:=fun U=>∑u:Grid,weight₀ u*filed₀ i mi (L u) U (Q u)
    ∃h:Coefficient field₀ (R.family.side i per),h.Format 0 stencil (Ψ i) ∧
      h.remBound 0 (Ψ i) (κ i) (variation₀*expense) ∧
      (field₀).coeffSize h.x ≤ variation₀*(unit₀*g₀^target) ∧
      (∀U,h.density 0 section₀ (Ψ i) U=prior U-((Ψ i).eval U:ℂ)*filed U) ∧
      WilsonThermometerCompulsoryReturn.Heard R (top:=N)
        (fun U=>prior U/((Ψ i).eval U:ℂ)-filed U-account h (Ψ i) U/((Ψ i).eval U:ℂ))
        (‖h.x 0‖+variation₀*expense) ∧
      (∀U,h.density 0 section₀ (Ψ i) U-(soft h).density 0 section₀ (canon i) U=account h (Ψ i) U) ∧
      ∀U,account h (Ψ i) U≠0 → ∃j,h.forced j U≠0 ∧ 0∈((canon i).activities.forced j).support ∧
        ∃v,v∈((canon i).activities.forced j).inventory ∧ v∈flags (canon i).p.threshold U := by
  classical
  intro live g₀ expense
  have perCell (u:Grid):=WilsonThermometerAncestralCapture.original R simple A top (home₀ u) hk D tab π Γ Ψ
    books ahead order shelf seats W mt (inlet u) (counted u) refs path pass month fits packed q l degree cap deep
    aged late weak mi both days booked (oldRent u) (start u) way station sec slow ready early activated force opening
    saved stripGrant depth H cap₀ hc fit heard fund target surplus (born u) profile r room space u.val rfl u.property support
  choose L reached roots entry using perCell
  let Q (u:Grid):=material₀ i live (L u) (a u)
  let raw (u:Grid) (U:Config G (R.family.side i per)):=original₀ live u U (Q u)
  let unmasked (u:Grid) (U:Config G (R.family.side i per)):=filed₀ i mi (L u) U (Q u)
  have reading (u:Grid):=entry u (a u) (z u) (allow u) (inside u)
  choose h fmt price size eq old split owned using fun u=>(reading u).2
  refine ⟨L,Q,?_,?_⟩
  · intro u
    have w:=WilsonThermometerAncestralLastWallet.original R simple A top (home₀ u) hk D tab π Γ Ψ
      books ahead order shelf seats W mt (inlet u) (counted u) q refs mi (by omega) (L u) (reached u)
      degree l cap slow days weak booked (oldRent u) (start u)
    refine ⟨reached u,roots u,w,rfl,(reading u).1,?_⟩
    let f:=WilsonCoeffUV.repeatF (sheet i)
    let v:=PhysicalWilsonPeriodizedProgram.branch (sheet i)
    have inv:=(eventually_atTop.mp (WilsonThermometerCenteredCompensation.original R simple D φ stripGrant order shelf
      k seats depth H cap₀ hc)).choose_spec i heard A hk fit tab π Γ Ψ W.course books W.scroll W.chamber fund
      mi live (home₀ u) ahead (L u) (a u) (z u) (allow u) (inside u) f v
    have eqQ:Order.value (g₀:ℂ) (Order.ratio (Bulk.Fk (topPost i live) f v (roster i (L u)) ((base i) (a u)) order))=Q u := (reading u).1 f v
    rw [←eqQ]
    exact inv.1
  · intro prior filed
    have div:0<κ i:=Real.sqrt_pos.mpr (allowance_pos R.family.path.levels.clock i)
    have law:=(W.course.1.walk i mi live.le).truep.valid
    obtain ⟨whole,shape,paid,coords,density⟩:=WilsonFullFaceTestedSum.cells (Ψ i) section₀ stencil 0
      div law (fun u:Grid=>weight₀ u) raw unmasked h fmt price size eq
    have variation:=WilsonThermometerSupportedCells.variation (N:=N) (per:=per) R r profile
    have gp:=((eventually_atTop.mp (WilsonThermometerAncestralCalendar.weak R simple)).choose_spec i weak N per
      (i+1) (by omega) (by omega)).1
    have exp0:0 ≤ expense := by dsimp [expense,g₀];positivity
    have unit0:0 ≤ unit₀*g₀^target := mul_nonneg (abs_nonneg _) (pow_nonneg gp.le _)
    have budget:whole.remBound 0 (Ψ i) (κ i) (variation₀*expense) :=by
      obtain ⟨a₀,a₁,h₀,h₁,n,tail⟩:=paid
      exact ⟨a₀,a₁,h₀,h₁,n.trans (mul_le_mul_of_nonneg_right variation exp0),tail⟩
    have same:∀U,whole.density 0 section₀ (Ψ i) U=prior U-((Ψ i).eval U:ℂ)*filed U:=density
    exact ⟨whole,shape,budget,coords.trans (mul_le_mul_of_nonneg_right variation unit0),same,
      WilsonMeasuredSignedScalar.original R simple π Γ Ψ W.course mi live.le 0 whole shape budget prior filed same⟩

end YM.Integration.WilsonThermometerAncestralTest
