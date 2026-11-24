import YM.Integration.WilsonThermometerWardCourseResponse

/-! The earlier original Wilson scalar with an order-independent restored physical-source wage. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerWardShoulderResponse
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
def Paid (q loss:ℕ) (offer:((J).Mode→ℂ)→ℝ) (sites:Fin 3→Site ((C).side N per)) (vec:(l:Fin 3)→(C).label (ages l)):Prop:=
    ∀ (_ : (∑j,ages j) ≤ 14) (_ : WayStation R.kit) (_ : WilsonCenteredCaptureClock.first R simple ≤ i)
    (_ : R.t 0 ≤ i)
    (slow : ∀ j, ((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (ready : WilsonReportLampForecast.Ready R.family.path.levels)
    (_ : (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (_ : (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (_ : Pass D bank R.alloy R.kit) (_ : MintClock.Hospital D R.rolls bank R.kit.target φ books ahead R.alloy.delay)
    (_ : shelf≤R.alloy.B.a.clock.J i) (_ : P.op.count≤Burn.horizon k+2)
    (_ : q≤R.alloy.B.a.clock.J i) (deep : 2*(q+1)+8≤order) (aged : q+4≤3*k+2)
    (_ : WilsonFirstReceivedEarnedFee.opening R simple P.op.count q order k deep aged (by norm_num:0<(1/4:ℝ)) ≤ i)
    (c : (J).Mode → ℂ) (y : Site ((C).side i per)) (Z : Support ((C).side i per)) (_ : y∈Z)
    (_ : ∀j:Fin 3,homes j∈Z) (rad : ℕ) (_ : ∀j:Fin 3,separation (homes j) y≤rad)
    (_ : rad≤(Ψ i).p.B) (_ : Z⊆halo (Ψ i).p.B {y}) (α : ℝ) (_ : (Ψ i).p.supportExponent≤α)
    (target : ℕ) (_ : target+(loss+87)≤q)
    (_ : WilsonCapturedPrimaryPaid.grade (depth 0 target) 0 1 +(loss+6)≤q)
    (_ : (eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple q)).choose ≤ i)
    (_ : 1≤(R.family.path.levels.budget i).supportExponent)
    (_ : (eventually_atTop.mp (Trace.Physical.GermGraph.cut_flat R.family simple 0)).choose ≤ i)
    (_ : (eventually_atTop.mp (WilsonCapturedPrimaryOnRun.readouts R simple (F) (Y) (S)
      (depth 0 target) 0 1 le_rfl)).choose ≤ i)
    (_ : (eventually_atTop.mp (WilsonCapturedPrimaryTariff.original R simple 0 0 target 0 0 slow)).choose ≤ i)
    (_:TicketP R.alloy R.kit D bank) (_:m≤u) (earlier:u ≤ i)
    (_:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ))≤u)
    (_:j≤u) (_:Opened (C) 0 u per)
    (Yₛ:(J).Mode→sources) (_:∀s,Continuous (Yₛ s)) (fare:(J).Mode→ℝ)
    (_:∀s:(J).Mode,Booked (C) N per 0 (wardField sites vec s) u (earlier.trans cut.le))
    (_:∀s,PaidAt (C).S N per j ((C).beta N per) (fare s)
      (Yₛ s-report R (wardField sites vec s) u • (1:sources))),
    let wallet:=offer c
    let K:ℝ:=1
    let tape:=AllOrder.Floe.Step.tape (Burn.horizon k+2)
    let issued:=Air.craft student (fun z=>(student z).paint fired) ages (π i) tape
    let nominal:=fun U=>Poly.pass (Integral.markedLog g U issued)
    let R₀ := |M α| * wallet * (K+4^q+1)
    let A₀ := 192*(Fintype.card (Multi.parts (J)).Mode:ℝ)*wallet*K
    let wrap := WilsonCapturedPrimaryCoreBill.wrapFee (F) (Y)
    let I := WilsonCapturedPrimaryDecoder.invoice (F) (Y) 0
    let fieldFee := 2*I*(A₀+(4*wrap+1)*R₀)+wrap*R₀
    let model:=fun U=>((Ψ i).eval U:ℂ)*take c (nominal U)
    ‖(∑s,(c s)*(C).omega N per (Yₛ s))-
      WilsonThermometerUnitFilingCoarse.reading R (N:=N) model u earlier‖≤
      (∑s,‖c s‖*fare s)+(fieldFee+5*R₀)*g^target 


include simple course cut in
theorem original (q loss:ℕ) (offer:((J).Mode→ℂ)→ℝ) (sites:Fin 3→Site ((C).side N per))
    (vec:(l:Fin 3)→(C).label (ages l))
    (sold:∀c:(J).Mode→ℂ,g^loss*weightBill c P.w≤offer c)
    (funded:debt (1/4) q≤g^q)
    (before:physical fired=gust (C).path N per N (WilsonCapturedPrimaryWardAppointment.input R ages sites vec (J))
      (i+1) cut) (gp:0≤g) (unit:g≤1):
    Paid (j:=j) (u:=u) R simple cut hk D bank π Γ Ψ books hi ahead order shelf seats
      actors pieces ages physical P fired q loss offer sites vec :=by
  intro gradeCap way station sec slow ready early late pass hospital narrow load force deep aged opened c y Z center
    h₀ rad near radius box α strength target surplus nodeOrder saved healthy wrapped panelDate tariffDate ticket floor
    earlier gate ju door fields cont fare booked covered
  have estimate:=WilsonThermometerWardCoveredStop.original R simple cut hk D bank π Γ Ψ course books hi ahead
    order shelf seats actors pieces ages physical P fired gradeCap way station sec slow ready early late pass hospital
    narrow load q q force deep aged (by norm_num:0<(1/4:ℝ)) opened (funded.trans (pow_le_one₀ gp unit)) c y Z center
    h₀ rad near radius box α strength loss (offer c) 1 (sold c) target surplus nodeOrder (by simpa only [one_mul] using funded)
    saved healthy wrapped panelDate tariffDate ticket floor earlier gate ju door ages sites vec
    (WilsonCapturedPrimaryWardAppointment.input R ages sites vec (J))
    (WilsonCapturedPrimaryWardAppointment.paid R ages sites vec (J)) before (fun _=>1)
    (fun s=>by simp) fields cont fare booked covered
  simpa only [mul_one] using estimate
end YM.Integration.WilsonThermometerWardShoulderResponse
