import YM.Integration.WilsonThermometerRegisteredCenteredSmooth
import YM.Integration.WilsonThermometerRegisteredCenteredReflection
import YM.Integration.WilsonThermometerNominatedConnectedStop

/-! The full compact assay on its original reflected Wilson run, including the signed fixed-stop model, every occupied mask and the six proper centered corrections. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCenteredStop
universe u
set_option maxHeartbeats 200000
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
local notation "Side₀" => Site (R.family.side N per)
local notation "UV₀" => ((N,per):UVIndex)
local notation "Grid" => {u:(Side₀)×(Side₀)//WilsonThermometerRegisteredAbsoluteRoom.mass R r UV₀ profile u≠ 0}
local notation "fineW" x:max => WilsonSeparatedOriginalThermometerCells.weight profile (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r UV₀) x
local notation "Fine" => {x:Fin 3→(Side₀)//fineW x≠ 0}
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

open MSbar.Heath WilsonJointAxialRoster WilsonJointAxialHearing WilsonReceivedWholeFieldHot
open Primitives.GCC.Anchor WilsonReportingForestAngularFare WilsonRegisteredAxialRates WilsonRegisteredAffineHalo WilsonRootedKioskOccupiedSlip
local notation "width₀" => (order+shelf+2)
local notation "reader" i:max mi:max L:max => Air.craft
  (Oak.student (n:=per) R hk D tab π Γ books mi (L).op (L).lesson ahead WilsonThermometerCourseHearing.disks (L).model order (L).voter)
  (fun v=>((Oak.student (n:=per) R hk D tab π Γ books mi (L).op (L).lesson ahead WilsonThermometerCourseHearing.disks (L).model order (L).voter) v).paint fired)
  ages (π i) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
local notation "cost₀" p:max l:max => WilsonReceivedCloseOrdinaryGrade.invoice (J₃) (Fintype.card (Fin 3)) 0
    (p+(3+(l+2))) 1+(4:ℝ)^(p+(3+(l+2))+1+2*width₀*(Fintype.card (Fin 3)))*
      (Fintype.card (Multi.parts (J₃)).Mode)*((2:ℝ)^width₀)^(Fintype.card (Fin 3))

open WilsonThermometerFiniteConnectedCells WilsonThermometerRegisteredAncestralProperStore
open Function Set Filter Finset Marker Extra.Trajectories Primitives.GCC.Anchor
open Lattice Laurent Exterior Wilson RG Precision Tree Matrix Bloch FormalBulk08 FormalBulk08.Flat
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonCoeffUV.Soil WilsonCoeffUV.Shard WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider PhysicalNext.Repeat.Legato Labels Source Next.Foundations
open WilsonConditionalTaylorWheelConnectedReadout WilsonThermometerCenteredAlgebra
open Extraction Table Spec Climb Trace.Pilot Next.UVStress Next.Rank RG12 RG17 PhysMS
open XSpace XSpace.Normalize XSpace.Rose WilsonPositionThermometerCapStation
open RG17 PhysMS Table Spec
local notation "wallet₀" i:max L:max => (fun v=>g (i+1)*(L).w v)
local notation "damp" i:max L:max obs:max tab₀:max => WilsonThermometerRegisteredCenteredInvoice.restoration (wallet₀ i L) obs tab₀
local notation "testₚ" i:max L:max obs:max Q:max => WilsonThermometerRegisteredCenteredInvoice.tested (wallet₀ i L) obs Q
local notation "actualBill" u:max live:max mi:max L:max q:max target:max tab₀:max h:max =>
  Bill R A simple live (home₀ u) hk D tab π Γ Ψ books mi ahead order shelf seats L q target 0 100 tab₀ h
local notation "priorₚ" u:max live:max mi:max L:max J:max axes:max q:max obs:max tab₀:max b:max h:max =>
  WilsonThermometerRegisteredCenteredMeasured.older R A simple live (home₀ u) hk D tab π Γ Ψ books mi ahead order shelf
    seats L J axes q obs tab₀ b h

local notation "cell" x:max => WilsonThermometerRegisteredAncestralProperTest.key (N:=N) (per:=per) R r profile x
variable {i:ℕ}

open RG05Readout.Address
open Trace.Physical.GermGraph OPE.Cards OPE.Log WilsonCapturedPrimaryFiledArms WilsonCapturedPrimaryNamedReturn
open WilsonThermometerUnitFilingNamedFaces WilsonThermometerOwnOffsetField RG05Readout
local notation "F" => R.family.labels.level 0
local notation "corr" obs:max Q:max => WilsonThermometerRegisteredCenteredInvoice.properInvoice obs Q
local notation "pupil₀" i:max mi:max L:max U:max => Poly.pass (WilsonRootedKioskOccupiedSlip.bare (lamps i mi L) WilsonThermometerCourseHearing.fired U)
local notation "coefficients₀" T:max => WilsonThermometerNominatedConnectedStop.coefficients T
local notation "grades₀" => WilsonThermometerUnitFilingNamedFaces.grades
local notation "UVin" A:max sec:max kn:max s:max => WilsonThermometerRegisteredCenteredReflection.own R (p:=per) A sec kn s

variable {f:Extraction.Order} {H₁:(Bel R.family.book).Hierarchy}
include simple in
theorem on_course (checks:A.station.checked f H₁ A.horizon) (unit:∀j,A.change j ((Bel R.family.book).unit j)=(Bel R.family.book).unit j)
    (active:A.station.k<N) (refs:∀v:Fin 3,R.family.ref (grade v) ≤ N)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (way:WayStation R.kit) (ticket:TicketP R.alloy R.kit D tab)
    {i j u z:ℕ} (mi:m ≤ i) (live:i<N) (floor:m ≤ u) (atStop:u ≤ i) (ju:j ≤ u) (kn:z ≤ N)
    (gate:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ))≤u)
    (door:Opened R.family 0 u per) (qual:WilsonThermometerUnitFilingShapeReceived.Qualified R A simple UV₀)
    (K:ℝ) (reflected:WilsonThermometerRegisteredCenteredReflection.Issued R profile K r j per (atStop.trans live.le) kn)
    (L:∀c:Grid,post i mi (offer₀ live c)) (q p:ℕ) (J:Voice G) (axes:Lattice.Order) (C₀:ℝ)
    (caps:Fin 3→ℕ) (admit:∀v,WilsonOriginalThermometerPalette.levels v<caps v) (phase:Fin 3→ℂ→ₗ[ℝ] ℝ)
    (birth:ℕ) (dated:birth≤N) (volume:Side) (lift:Side₀ → Cover) (test:Case caps)
    (sense:∀s:(J₃).Mode,(s.val→Side₀)→PChart G volume→ₗ[ℝ] ℂ)
    (issued:WilsonThermometerRegisteredCenteredSmooth.submitted R simple A hk D tab π Γ Ψ books ahead order shelf seats r profile
      live mi L q p J axes C₀ caps admit phase birth dated volume lift test sense):
    let obs:=measured R A UV₀
    let Q:=fun x:Fin 3→Side₀=>Poly.pass (WilsonThermometerNominatedDeletion.filed R A caps admit phase birth volume lift test sense x)
    let C:=fun x:Fine=>corr (obs x.val) (Q x.val)
    let model:=fun (x:Fine) (U:Config G (R.family.side i per))=>((Ψ i).eval U:ℂ)*((pupil₀ i mi (L (cell x)) U)*(C x)).part full
    let price₂:ℝ:=unit₀*(g (i+1))^(p+1)+5*(|fee (J₃)*stage₀ 100| *(4^q+2)*(g (i+1))^(p+1))
    let ratio:=fun x:Fine=>(damp i (L (cell x)) (obs x.val) (Q x.val):ℂ)
    ∃(V:Fine→(a:Fin 3)→Sight R.family (grades₀ a) per) (sec:Fine→(a:Fin 3)→Emblems R.family (grades₀ a)),
    (∀x,entered R grades₀ (WilsonThermometerAlignedCells.atOrigin (WilsonThermometerAlignedCells.offsets x.val)) (k:=z) (V x) (sec x)) ∧
    ‖profile.applyTo (WilsonPositionThermometerGradedReading.full r A UV₀)-WilsonThermometerFiniteConnectedCells.reference R UV₀ r profile Q-
       ∑x:Fine,fineW x.val*(WilsonThermometerUnitFilingCoarse.reading R (N:=N) (model x) u atStop-((Q x.val)*(C x)).part full)‖≤
      ∑x:Fine,‖fineW x.val‖*((∑s:(J₃).Mode,‖(coefficients₀ (C x)) s‖*(rent R grades₀ (UVin A (sec x) kn s)*(K*r^(1/32:ℝ))))+
        (‖ratio x‖+‖1-ratio x‖)*price₂):=by
  intro obs Q C model price₂ ratio
  obtain ⟨b,h,receipts,_⟩:=issued
  choose V sec resident arms using fun x:Fine=>reflected x.val x.property
  refine ⟨V,sec,resident,?_⟩
  have qu(x:Fin 3→Side₀):(Q x).part (J₃).quiet=1:=
    Poly.pass_part _ ((WilsonThermometerNominatedDeletion.nominated R A simple dated caps admit phase volume lift test sense).2.1 x)
  apply WilsonThermometerRegisteredCenteredSum.tested R A checks unit UV₀ active refs r profile Q qu
  intro x
  let loc:=home₀ (cell x)
  have site:loc.origin=WilsonThermometerAlignedCells.atOrigin (WilsonThermometerAlignedCells.offsets x.val):=rfl
  let fare : (J₃).Mode → ℝ:=fun s=>(rent R grades₀ (UVin A (sec x) kn s)*(K*r^(1/32:ℝ)))
  exact WilsonThermometerNominatedConnectedStop.original R A simple live loc hk D tab π Γ Ψ course books mi ahead
    order shelf seats (L (cell x)) way ticket floor atStop gate ju door qual x.val site refs q (p+1) 100 0 (Q x.val)
    (qu x.val) checks unit active (receipts x).1 fare (fun s _=>arms x A loc site refs s)

end YM.Integration.WilsonThermometerRegisteredCenteredStop
