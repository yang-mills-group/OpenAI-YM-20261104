import YM.Integration.WilsonThermometerRegisteredCenteredFixedInvoice
import YM.Integration.WilsonThermometerRegisteredCenteredFold
import YM.Integration.WilsonThermometerUnitFilingPupilClock
/- The original two compensated physical filings on the same logarithmic stop window. -/
import YM.Integration.WilsonThermometerUnitFilingPupil

/-! The same entire filed pupil can be stopped within the funded perturbative interval. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCenteredWindow
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
open WilsonThermometerUnitFilingPupilClock
local notation "Q1" A:max => WilsonThermometerRegisteredCenteredFixedInvoice.tested A
local notation "wgt" j:max L:max => (fun a=>g (j+1)*(L).w a)
local notation "rowP" j:max mj:max L:max Q:max => fun U:Config G (R.family.side j per)=>
  ((canon j).eval U:ℂ)*∑c:Grid,weight₀ c*filed₀ j mj (L c) U Q

theorem original {i u:ℕ} (live:i < N) (mi:m ≤ i) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (L:∀c:Grid,post i mi (offer₀ live c))
    (positions:∀c:Grid,∀a,(homes i (L c)) a=(R.family.S.toDepth live.le per).parent ((home₀ c).origin a))
    (loss:ℕ) (genuine:∀c:Grid,(g (i+1))^loss ≤ Poly.toll (L c).w full)
    (capped:∀(c:Grid) (j:Fin 3),0<(wgt i (L c)) j ∧ (wgt i (L c)) j≤1)
    (means:∀v:Fin 3,‖WilsonThermometerCenteredScalar.read (WilsonThermometerFiniteConnectedCells.measured R A (N,per) fun _=>0) {v}‖≤1)
    (cu:R.family.ref 0 ≤ u) (ui:u ≤ i) (ou:Opened R.family 0 u per)
    (sec:R.t 0 ≤ i) (station:WilsonCenteredCaptureClock.first R simple ≤ i)
    (slow:∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (early:(eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (late:(eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (pass:Pass D tab R.alloy R.kit) (hospital:MintClock.Hospital D R.rolls tab R.kit.target φ books ahead R.alloy.delay)
    (narrow:shelf ≤ R.alloy.B.a.clock.J i) (seated:seats ≤ Burn.horizon k+2)
    (weak:(eventually_atTop.mp (WilsonThermometerAncestralCalendar.weak R simple)).choose ≤ i)
    (room:(eventually_atTop.mp (WilsonThermometerRegisteredTripleRoom.spatial R simple profile)).choose ≤ i)
    (q:ℕ) (issued:start R simple slow u loss q ≤ i) (ov:Opened R.family 0 (date R simple slow u loss q i issued) per)
    (space:|r| ≤ R.family.S.a i) (support:(R.family.path.levels.budget i).supportExponent ≤ 100):
    let v:=date R simple slow u loss q i issued
    let vi:= (range R simple slow u loss q i issued).2.1.le
    let E:=variation₀*(fee J₃*WilsonPlantedOrdinaryHalo.master section₀ stencil 100 ((2:ℝ)^(order+shelf+2)))
    let hub:=WilsonThermometerFiniteConnectedCells.measured R A (N,per) (fun _=>0)
    let oneField:=rowP i mi L (1:Poly J₃)
    let secondField:=rowP i mi L (Q1 hub)
    let assay:=fun (j:ℕ) (ji:j ≤ i)=>12*reading R (N:=N) secondField j ji-11*reading R (N:=N) oneField j ji
    ‖assay u ui-assay v vi‖≤920*(2*E+1)*(g (i+1))^q:=by
  intro v vi E hub oneField secondField assay
  have funds(c:Grid):=WilsonThermometerRegisteredCenteredFixedInvoice.affordable hub (wgt i (L c))
    (fun j=>(capped c j).1) (fun j=>(capped c j).2) means
  have baseFee:=WilsonThermometerUnitFilingPupilClock.original R simple A hk D tab π Γ Ψ books ahead order shelf seats
    r profile live mi course L (fun _=>1) positions loss genuine (fun c=>(funds c).1) cu ui ou sec station
    slow ready early late pass hospital narrow seated weak room q issued ov space support
  have secondFee:=WilsonThermometerUnitFilingPupilClock.original R simple A hk D tab π Γ Ψ books ahead order shelf seats
    r profile live mi course L (fun _=>Q1 hub) positions loss genuine (fun c=>(funds c).2) cu ui ou sec station
    slow ready early late pass hospital narrow seated weak room q issued ov space support
  let cutoff:ℝ:=40*(2*E+1)*(g (i+1))^q
  have bound₀:‖reading R (N:=N) oneField u ui-reading R (N:=N) oneField v vi‖≤cutoff:=baseFee
  have bound₁:‖reading R (N:=N) secondField u ui-reading R (N:=N) secondField v vi‖≤cutoff:=secondFee
  have eq:assay u ui-assay v vi =
      12*(reading R (N:=N) secondField u ui-reading R (N:=N) secondField v vi)-
      11*(reading R (N:=N) oneField u ui-reading R (N:=N) oneField v vi):=by dsimp only [assay];ring
  rw [eq];apply (norm_sub_le _ _).trans
  rw [norm_mul,norm_mul,show ‖(12:ℂ)‖=(12:ℝ) by norm_num,show ‖(11:ℂ)‖=(11:ℝ) by norm_num]
  dsimp only [cutoff] at bound₀ bound₁;linarith

end YM.Integration.WilsonThermometerRegisteredCenteredWindow
