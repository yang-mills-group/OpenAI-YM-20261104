import YM.Integration.WilsonThermometerUnitFilingRawSum
import YM.Integration.WilsonThermometerRegisteredCenteredFixedInvoice
import YM.Integration.WilsonThermometerRegisteredCenteredFold
import YM.Integration.WilsonThermometerUnitFilingPupilClock
/- The original two compensated physical filings on the same logarithmic stop window. -/
import YM.Integration.WilsonThermometerUnitFilingPupil

/-! The same entire filed pupil can be stopped within the funded perturbative interval. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCenteredWindowField
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
open WilsonThermometerUnitFilingPupilClock WilsonThermometerRegisteredCenteredInvoice
local notation "Q1" A:max => WilsonThermometerRegisteredCenteredFixedInvoice.tested A
local notation "wgt" j:max L:max => (fun a=>g (j+1)*(L).w a)
local notation "rowP" j:max mj:max L:max Q:max => fun U:Config G (R.family.side j per)=>
  ((canon j).eval U:ℂ)*∑c:Grid,weight₀ c*filed₀ j mj (L c) U Q

local notation "chargeP" i:max mi:max L:max U:max table:max =>
  ((Poly.pass (WilsonRootedKioskOccupiedSlip.bare (lamps i mi L) WilsonThermometerCourseHearing.fired U))*table).part full

theorem original {i:ℕ} (live:i < N) (mi:m ≤ i) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (L:∀c:Grid,post i mi (offer₀ live c))
    (positions:∀c:Grid,∀a,(homes i (L c)) a=(R.family.S.toDepth live.le per).parent ((home₀ c).origin a))
    (loss:ℕ) (genuine:∀c:Grid,(g (i+1))^loss ≤ Poly.toll (L c).w full)
    (capped:∀(c:Grid) (j:Fin 3),0<(wgt i (L c)) j ∧ (wgt i (L c)) j≤1)
    (means:∀v:Fin 3,‖WilsonThermometerCenteredScalar.read (WilsonThermometerFiniteConnectedCells.measured R A (N,per) fun _=>0) {v}‖≤1)
    (ci:R.family.ref 0 ≤ i)
    (sec:R.t 0 ≤ i) (station:WilsonCenteredCaptureClock.first R simple ≤ i)
    (slow:∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (early:(eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (late:(eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (pass:Pass D tab R.alloy R.kit) (hospital:MintClock.Hospital D R.rolls tab R.kit.target φ books ahead R.alloy.delay)
    (narrow:shelf ≤ R.alloy.B.a.clock.J i) (seated:seats ≤ Burn.horizon k+2)
    (room:(eventually_atTop.mp (WilsonThermometerRegisteredTripleRoom.spatial R simple profile)).choose ≤ i)
    (space:|r| ≤ R.family.S.a i) (support:(R.family.path.levels.budget i).supportExponent ≤ 100):
    let hub:=WilsonThermometerFiniteConnectedCells.measured R A (N,per) (fun _=>0)
    let invoice:=properInvoice hub (1:Poly J₃)
    let A₀:=rowP i mi L (1:Poly J₃)
    let A₁:=rowP i mi L (Q1 hub)
    let model:=fun (c:Grid) (U:Config G (R.family.side i per))=>
      ((Ψ i).eval U:ℂ)*(chargeP i mi (L c) U invoice)
    ∀{j:ℕ} (ji:j ≤ i),∑c:Grid,weight₀ c*reading R (N:=N) (model c) j ji =
      12*reading R (N:=N) A₁ j ji-11*reading R (N:=N) A₀ j ji:=by
  classical
  intro hub invoice A₀ A₁ model j ji
  let Z:=Config G (R.family.side i per)
  let gross:=fee J₃ * WilsonPlantedOrdinaryHalo.master section₀ stencil 100 ((2:ℝ)^(order+shelf+2)) / (g (i+1))^(3+loss+61)
  have proofRep:=R.makes.wilson.represents N per i live.le
  have shape:(canon i).p=R.family.path.levels.budget i:=proofRep.vac
  have stock(Q:Poly J₃) (inverse:∀c:Grid,Poly.price (wgt i (L c)) (inverseMass Q) ≤ fee J₃):∀c:Grid,WilsonCenteredFiledAtoms.Store (canon i) section₀ stencil 0 (κ i) gross
    (fun U=>((canon i).eval U:ℂ)*(filed₀ i mi (L c) U Q)):=by
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
      order shelf seats (L c) ci sec station slow ready early late pass hospital narrow
      ((L c).capacity.le.trans seated) 0 _ center anchors (canon i).p.B near le_rfl (by rfl)
      100 (shape.symm ▸ support) Q loss (genuine c) (inverse c)
  let localF (Q:Poly J₃) (c:Grid) (U:Z):ℂ:=((canon i).eval U:ℂ)*filed₀ i mi (L c) U Q
  have funds(c:Grid):=WilsonThermometerRegisteredCenteredFixedInvoice.affordable hub (wgt i (L c))
    (fun j=>(capped c j).1) (fun j=>(capped c j).2) means
  have integrable(Q:Poly J₃) (afford:∀c:Grid,Poly.price (wgt i (L c)) (inverseMass Q) ≤ fee J₃) (c:Grid):
      Integrable (localF Q c) (prior G _):=by
    obtain ⟨h,fit,rem,eq⟩:=stock Q afford c
    exact ((h.envelope section₀ proofRep.good rem fit).integrableC (prior G _)).congr (Eventually.of_forall eq)
  have collapse(Q:Poly J₃):
      (∑c:Grid,weight₀ c • localF Q c)=rowP i mi L Q:=by
    funext U
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,localF,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro c _;ring
  have filed(Q:Poly J₃) (afford:∀c:Grid,Poly.price (wgt i (L c)) (inverseMass Q) ≤ fee J₃):
      ∑c:Grid,weight₀ c*reading R (N:=N) (localF Q c) j ji=reading R (N:=N) (rowP i mi L Q) j ji:=by
    rw [←collapse Q]
    exact (WilsonThermometerUnitFilingRawSum.family R (N:=N) univ (fun c:Grid=>weight₀ c) (localF Q) (integrable Q afford) ji).2.symm
  have quiet:(Ψ i).eval=(canon i).eval:=(QuadraticLocal.Advent.later R π Γ Ψ course mi live.le).view
  have expand(c:Grid):model c=(12:ℂ) • localF (Q1 hub) c+(-11:ℂ) • localF 1 c:=by
    funext U
    change ((Ψ i).eval U:ℂ)*(_*invoice).part full=12*localF (Q1 hub) c U+-11*localF 1 c U
    rw [quiet,WilsonThermometerRegisteredCenteredFixedInvoice.reading]
    dsimp only [localF];ring
  have cell(c:Grid):reading R (N:=N) (model c) j ji=
      12*reading R (N:=N) (localF (Q1 hub) c) j ji-11*reading R (N:=N) (localF 1 c) j ji:=by
    have first:=integrable (Q1 hub) (fun c=>(funds c).2) c
    have zero:=integrable 1 (fun c=>(funds c).1) c
    rw [expand,WilsonThermometerUnitFilingRaw.add R _ _ (first.smul (12:ℂ)) (zero.smul (-11:ℂ)) ji,
      WilsonThermometerUnitFilingRawSum.scaled R 12 _ first ji,WilsonThermometerUnitFilingRawSum.scaled R (-11) _ zero ji]
    ring
  calc
    _=∑c:Grid,(12*(weight₀ c*reading R (N:=N) (localF (Q1 hub) c) j ji)-11*(weight₀ c*reading R (N:=N) (localF 1 c) j ji)):=by
      apply Finset.sum_congr rfl;intro c _;rw [cell];ring
    _=_:=by rw [sum_sub_distrib,←mul_sum,←mul_sum,filed _ (fun c=>(funds c).2),filed _ (fun c=>(funds c).1)]
end YM.Integration.WilsonThermometerRegisteredCenteredWindowField
