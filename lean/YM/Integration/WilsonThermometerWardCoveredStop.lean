import YM.Integration.WilsonGeometricSignedCoveredReturn
import YM.Integration.WilsonThermometerWardSignedStop
import YM.Integration.WilsonThermometerWardPostedIncome

/-! A genuine cutoff Ward source on the actual post, its finite covered word and its earlier scalar reading. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerWardCoveredStop
open MergeProof.Accent
open FVA1 Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Function Filter MeasureTheory Finset Lattice Wilson RG Source Labels Marker QuadraticLocal
open Extra.Histories Extra.Histories.Relay Extra.Trajectories Extra.Multi MergeProof MergeProof.Accent
open PhysicalNext.Repeat.Legato AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit
open WheelP QuadraticLocal.Advent FVA1 RG12 RG16 RG16.Literal
open Table Spec Trace Trace.Pilot Extraction Climb Next.UVStress Trace.Physical.GermGraph Cells
open WilsonThermometerCourseIntake WilsonGeometricSignedCapture WilsonThermometerFiniteConnectedCells
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFeed
open WilsonPositionThermometerCapStation PhysMS RG17 OPE.Cards
open PhysicalNext PhysicalNext.Repeat Legato Org AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler
open RemainderComparison Tree

open WilsonThermometerCourseHearing WilsonThermometerCourseIntake WilsonPositionThermometerCapStation
open RG16.Literal Next.Rank Next.UVStress MergeProof.East OriginalForcedAddresses Exterior
open WilsonThermometerCenteredAlgebra WilsonGeometricSignedCapture
local notation "J" => Stock.census (Fin 3)
open Trace.Physical.Germ WilsonCapturedPrimaryReading
open WilsonGeometricSignedCoveredReturn

variable {G : Gauge} (R : Run G) (simple : G.Simple) {m i N per k u j : ℕ}
  (cut : i<N)
  (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (bank : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls bank φ) (hi : m ≤ i)
  (ahead : Mentor.Forecast D R.rolls bank φ books) (order shelf seats : ℕ)
variable {X : Fin 3 → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀v, Set (X v)) (pieces : ∀v, Submodule ℝ (X v)) (ages : Fin 3 → ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly J)
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D bank π Γ Ψ books ahead actors pieces ages
    order shelf seats i hi physical)
  (fired : Wallet actors)
local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D bank π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D bank π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D bank π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "gauge" => (Tint.Patrol.report student P.output oldG)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "width" => ((Ψ i).p.supportExponent+1+1)
local notation "modelFee" => Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count width (fig).limitC G
local notation "oldFee" => Earn.Earnings.hitPrice (fig) G (sheet).ratio.count (Ψ (i+1)).p (Ψ i).p
  (Ω⁻¹*P.cost) (Ω⁻¹*P.rent) (Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k) oldG
local notation "cash" => modelFee*((fig).produce (sheet).ratio.count*P.cost)
local notation "raw" => (((2:ℝ)^(order+shelf+1)/(oldG)^15)*cash)
local notation "g" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "βhat" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "rel" => R.alloy.B.a.clock.forcedAllowance i
local notation "weights" => Stoop.radius P.w (Ω^6)

local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "configuration" => Config G (R.family.side i per)
local notation "value" => LocalComparison.actualPush R.family N per i


local notation "C" => R.family
local notation "F" => R.family.labels.level 0
local notation "S" => R.family.localSection 0
local notation "Y" => R.family.params
local notation "μ" => (R.family.path.levels.params i).columns
local notation "incomingAt" => LocalComparison.actualPush R.family N per i (physical fired)

local notation "debt" => (fun (ε:ℝ) (p:ℕ)=>(8*Ω^P.op.count)*P.rent+ε*g^p)
local notation "B" => ((2:ℝ)^(order+shelf+2)+4)
local notation "shine" => (fun (q:ℕ)=>βhat^(-(q:ℝ)))
local notation "M" => (fun (α:ℝ)=>WilsonFullFaceSignedPower.constants (S) (Y) α B)

local notation "sources" => Cut (C) N per
local notation "wardField" sites:max vec:max s:max => (fun U=>∏ l∈(s).val,(C).O N per ((vec) l) ((sites) l) U)
include course cut in
theorem original (gradeCap : (∑j,ages j) ≤ 14) (way : WayStation R.kit) (station : WilsonCenteredCaptureClock.first R simple ≤ i)
    (sec : R.t 0 ≤ i)
    (slow : ∀ j, ((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (ready : WilsonReportLampForecast.Ready R.family.path.levels)
    (early : (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (late : (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (pass : Pass D bank R.alloy R.kit) (hospital : MintClock.Hospital D R.rolls bank R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf≤R.alloy.B.a.clock.J i) (load : P.op.count≤Burn.horizon k+2)
    (p q : ℕ) (force : q≤R.alloy.B.a.clock.J i) (deep : 2*(p+1)+8≤order) (aged : p+4≤3*k+2)
    {ε : ℝ} (positive : 0<ε) (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged positive ≤ i)
    (small : debt ε p≤1) (c : (J).Mode → ℂ) (y : Site ((C).side i per)) (Z : Support ((C).side i per)) (center : y∈Z)
    (homes_in : ∀j:Fin 3,homes j∈Z) (rad : ℕ) (near : ∀j:Fin 3,separation (homes j) y≤rad)
    (radius : rad≤(Ψ i).p.B) (box : Z⊆halo (Ψ i).p.B {y}) (α : ℝ) (strength : (Ψ i).p.supportExponent≤α)
    (loss : ℕ) (wallet K : ℝ) (bought : g^loss * weightBill c P.w ≤ wallet)
    (target : ℕ) (surplus : target+(loss+87)≤q)
    (nodeOrder : WilsonCapturedPrimaryPaid.grade (depth 0 target) 0 1 +(loss+6)≤q) (funded : debt ε p ≤ K*g^q)
    (saved : (eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple q)).choose ≤ i)
    (healthy : 1≤(R.family.path.levels.budget i).supportExponent)
    (wrapped : (eventually_atTop.mp (Trace.Physical.GermGraph.cut_flat R.family simple 0)).choose ≤ i)
    (panelDate : (eventually_atTop.mp (WilsonCapturedPrimaryOnRun.readouts R simple (F) (Y) (S)
      (depth 0 target) 0 1 le_rfl)).choose ≤ i)
    (tariffDate : (eventually_atTop.mp (WilsonCapturedPrimaryTariff.original R simple 0 0 target 0 0 slow)).choose ≤ i)
    (ticket:TicketP R.alloy R.kit D bank) (floor:m≤u) (earlier:u ≤ i)
    (gate:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ))≤u)
    (ju:j≤u) (door:Opened (C) 0 u per)
    (dims:Fin 3→ℕ) (sites:Fin 3→Site ((C).side N per)) (vec:(l:Fin 3)→(C).label (dims l))
    (cutoff:Config G ((C).side N per)→Poly J) (integrated:Integrable cutoff (prior G _))
    (before:physical fired=gust (C).path N per N cutoff (i+1) cut) (share:(J).Mode→ℂ)
    (bareFaces:∀s,(fun U=>(cutoff U).part s)=share s •
      (fun U=>(WilsonCapturedPrimaryWardAppointment.input R dims sites vec (J) U).part s))
    (Yₛ:(J).Mode→sources) (cont:∀s,Continuous (Yₛ s)) (fare:(J).Mode→ℝ)
    (booked:∀s:(J).Mode,Booked (C) N per 0 (wardField sites vec s) u (earlier.trans cut.le))
    (covered:∀s,PaidAt (C).S N per j ((C).beta N per) (fare s)
      (Yₛ s-report R (wardField sites vec s) u • (1:sources))) :
    let tape:=AllOrder.Floe.Step.tape (Burn.horizon k+2)
    let issued:=Air.craft student (fun z=>(student z).paint fired) ages (π i) tape
    let nominal:=fun U=>Poly.pass (Integral.markedLog g U issued)
    let R₀ := |M α| * wallet * (K+4^q+1)
    let A₀ := 192*(Fintype.card (Multi.parts (J)).Mode:ℝ)*wallet*K
    let wrap := WilsonCapturedPrimaryCoreBill.wrapFee (F) (Y)
    let I := WilsonCapturedPrimaryDecoder.invoice (F) (Y) 0
    let fieldFee := 2*I*(A₀+(4*wrap+1)*R₀)+wrap*R₀
    let model:=fun U=>((Ψ i).eval U:ℂ)*take c (nominal U)
    ‖(∑s,(c s*share s)*(C).omega N per (Yₛ s))-
      WilsonThermometerUnitFilingCoarse.reading R (N:=N) model u earlier‖≤
      (∑s,‖c s*share s‖*fare s)+(fieldFee+5*R₀)*g^target :=by
  classical
  intro tape issued nominal R₀ A₀ wrap I fieldFee model
  obtain ⟨h,fmt,money,field,_,stored⟩:=WilsonGeometricSignedCoveredReturn.original
    R simple cut hk D bank π Γ Ψ course books hi ahead order shelf seats actors pieces ages physical P fired
    gradeCap way station sec slow ready early late pass hospital narrow load p q force deep aged positive opened small c y Z center homes_in
    rad near radius box α strength loss wallet K bought target surplus nodeOrder funded saved healthy wrapped panelDate tariffDate
  have estimate:0≤R₀*g^target:=by obtain ⟨a,b,a0,b0,ab,_⟩:=money; exact (add_nonneg a0 b0).trans ab
  have scalar:‖h.x 0‖≤fieldFee*g^target:=
    (Finset.single_le_sum (fun l _=>norm_nonneg (h.x l)) (Finset.mem_univ 0)).trans stored
  have smooth (s:(J).Mode):Continuous (wardField sites vec s):=by
    apply continuous_finsetProd
    intro l _
    exact (C).continuousO N per _ _ _
  have agree (U:configuration):
      (∑s,(c s*share s)*credit (C) N per 0 (wardField sites vec s) i cut.le U)-model U =
        (1:ℂ)*h.density y (S) (Ψ i) U+0*h.density y (S) (Ψ i) U:=by
    rw [one_mul,zero_mul,add_zero,field]
    apply congrArg (fun z=>z-model U)
    apply Finset.sum_congr rfl
    intro s _
    have equal:=congrFun (WilsonThermometerWardPostedIncome.posted R dims sites vec cut cutoff integrated
      (physical fired) before s (share s) (bareFaces s)) U
    simpa only [Pi.smul_apply,smul_eq_mul,←mul_assoc] using (congrArg (fun z=>c s*z) equal.symm)
  letI : Nonempty (J).Mode := ⟨(J).quiet⟩
  have price:=WilsonThermometerWardSignedStop.original R simple way D bank ticket π Γ Ψ course cut.le floor earlier gate
    (fun s=>c s*share s) Yₛ (fun s=>wardField sites vec s) cont smooth fare ju door booked covered y model 1 0
    h h estimate estimate fmt fmt money money agree
  simp only [norm_one,norm_zero,one_mul,zero_mul,add_zero] at price
  have total : ‖h.x 0‖+5*(R₀*g^target)≤(fieldFee+5*R₀)*g^target := calc
    ‖h.x 0‖+5*(R₀*g^target) ≤ fieldFee*g^target+5*(R₀*g^target) := add_le_add scalar le_rfl
    _ = (fieldFee+5*R₀)*g^target := by ring
  exact price.trans (add_le_add le_rfl total)
end YM.Integration.WilsonThermometerWardCoveredStop
