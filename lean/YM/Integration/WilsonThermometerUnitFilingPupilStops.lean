import YM.Integration.WilsonThermometerUnitFilingEarnedJournal
import YM.Integration.WilsonThermometerUnitFilingPlanted

/-! The entire tested finite pupil at a fixed and a moving earlier filing. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPupilStops
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

open WilsonThermometerUnitFilingCoarse (reading)
open WilsonMacroscopicRichCaptureFilingBudget (capital)
theorem original {i u v:ℕ} (live:i < N) (mi:m ≤ i) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (L:∀c:Grid,post i mi (offer₀ live c)) (Q:Grid→Poly J₃)
    (positions:∀c:Grid,∀a,(homes i (L c)) a=(R.family.S.toDepth live.le per).parent ((home₀ c).origin a))
    (loss:ℕ) (genuine:∀c:Grid,(g (i+1))^loss ≤ Poly.toll (L c).w full)
    (inverse:∀c:Grid,Poly.price (fun j=>(g (i+1))*(L c).w j) (inverseMass (Q c)) ≤ fee J₃)
    (cu:R.family.ref 0 ≤ u) (uv:u ≤ v) (vi:v ≤ i) (ou:Opened R.family 0 u per) (ov:Opened R.family 0 v per)
    (sec:R.t 0 ≤ i) (station:WilsonCenteredCaptureClock.first R simple ≤ i)
    (slow:∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (early:(eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (late:(eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (pass:Pass D tab R.alloy R.kit) (hospital:MintClock.Hospital D R.rolls tab R.kit.target φ books ahead R.alloy.delay)
    (narrow:shelf ≤ R.alloy.B.a.clock.J i) (seated:seats ≤ Burn.horizon k+2)
    (weak:(eventually_atTop.mp (WilsonThermometerAncestralCalendar.weak R simple)).choose ≤ i)
    (room:(eventually_atTop.mp (WilsonThermometerRegisteredTripleRoom.spatial R simple profile)).choose ≤ i)
    (space:|r| ≤ R.family.S.a i) (support:(R.family.path.levels.budget i).supportExponent ≤ 100):
    let gross:=fee J₃ * WilsonPlantedOrdinaryHalo.master section₀ stencil 100 ((2:ℝ)^(order+shelf+2)) / (g (i+1))^(3+loss+61)
    let filed:=fun U=>∑c:Grid,weight₀ c*filed₀ i mi (L c) U (Q c)
    let pupil:=fun U=>((canon i).eval U:ℂ)*filed U
    ‖reading R (N:=N) pupil u (uv.trans vi)-reading R (N:=N) pupil v vi‖ ≤ 
      2*capital R.family i (variation₀*gross) 1*Real.exp (-(R.family.S.scale i-R.family.S.scale v)/8):=by
  classical
  intro gross filed pupil
  have proofRep:=R.makes.wilson.represents N per i live.le
  have shape:(canon i).p=R.family.path.levels.budget i:=proofRep.vac
  have spec:∀c:Grid,WilsonCenteredFiledAtoms.Store (canon i) section₀ stencil 0 (κ i) gross
    (fun U=>((canon i).eval U:ℂ)*(filed₀ i mi (L c) U (Q c))):=by
    intro c
    have near (a:Fin 3):separation ((homes i (L c)) a) 0 ≤ (canon i).p.B:=by
      rw [positions c a,shape]
      exact (eventually_atTop.mp (WilsonThermometerRegisteredTripleRoom.spatial R simple profile)).choose_spec i
        room N per live.le r space c.val c.property a
    have center:(0:Site (R.family.side i per))∈halo (canon i).p.B ({0}:Support _):=
      halo_spec.mpr ⟨0,Finset.mem_singleton_self _,by simp⟩
    have anchors (a:Fin 3):(homes i (L c)) a∈halo (canon i).p.B ({0}:Support _):=
      halo_spec.mpr ⟨0,Finset.mem_singleton_self _,by simpa only [separation_comm] using near a⟩
    exact WilsonThermometerPlantedScalar.original R A simple live (home₀ c) hk D tab π Γ Ψ course books mi ahead
      order shelf seats (L c) (cu.trans (uv.trans vi)) sec station slow ready early late pass hospital narrow
      ((L c).capacity.le.trans seated) 0 _ center anchors (canon i).p.B near le_rfl (by rfl)
      100 (shape.symm ▸ support) (Q c) loss (genuine c) (inverse c)
  choose h fmt paid eq using spec
  let sizeBill:=∑c:Grid,|(field₀).coeffSize (h c).x|
  have sizes (c:Grid):(field₀).coeffSize (h c).x ≤ sizeBill:=(le_abs_self _).trans  <|
    Finset.single_le_sum (fun j _=>abs_nonneg ((field₀).coeffSize (h j).x)) (Finset.mem_univ c)
  have div:0 < κ i:=Real.sqrt_pos.mpr (allowance_pos R.family.path.levels.clock i)
  obtain ⟨q,fit,budget,_,read⟩:=WilsonFullFaceTestedSum.cells (canon i) section₀ stencil 0 div proofRep.good
    (fun c:Grid=>weight₀ c) (fun c U=>((canon i).eval U:ℂ)*(filed₀ i mi (L c) U (Q c)))
    (fun _ _=>0) h fmt paid sizes (fun c U=>by simpa using eq c U)
  have gp:=((eventually_atTop.mp (WilsonThermometerAncestralCalendar.weak R simple)).choose_spec i weak N per
    (i+1) (Nat.le_succ i) live).1
  have fp:0≤fee J₃:=by
    unfold fee WilsonFiniteOrdinaryInverse.room
    exact Finset.sum_nonneg (fun n _=>pow_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg (fun a _=>by positivity))) n)
  have gross0:0≤WilsonPlantedOrdinaryHalo.master section₀ stencil 100 ((2:ℝ)^(order+shelf+2)):=by
    dsimp only [WilsonPlantedOrdinaryHalo.master];positivity
  have nonneg:0≤gross:=div_nonneg (mul_nonneg fp gross0) (pow_nonneg gp.le _)
  have purchased : q.remBound 0 (canon i) (κ i) (variation₀*gross):=by
    obtain ⟨a,b,na,nb,cap,remaining⟩:=budget
    exact ⟨a,b,na,nb,cap.trans (mul_le_mul_of_nonneg_right (WilsonThermometerSupportedCells.variation R r profile) nonneg),remaining⟩
  apply WilsonThermometerUnitFilingStops.two_stops R simple cu uv vi live.le ou ov
  refine ⟨q,fit,purchased,?_⟩
  intro U
  rw [read]
  dsimp [pupil,filed]
  simp only [mul_zero,Finset.sum_const_zero,sub_zero,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

end YM.Integration.WilsonThermometerUnitFilingPupilStops
