import YM.Integration.WilsonGeometricSignedMeasured
import YM.Integration.WilsonReceivedAxialFiling
import YM.Integration.WilsonGeometricSignedOrder
import YM.Integration.WilsonGeometricClearPost
import YM.Integration.WilsonGeometricPrimaryReturn

/-! The full finite coordinate of a funded signed capture on its one actual marked Wilson post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGeometricSignedCoveredReturn
open FVA1 Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

open WilsonThermometerCourseHearing WilsonThermometerCourseIntake WilsonPositionThermometerCapStation
open RG16.Literal Next.Rank Next.UVStress MergeProof.East OriginalForcedAddresses Exterior
open WilsonThermometerCenteredAlgebra WilsonGeometricSignedCapture
local notation "J" => Stock.census (Fin 3)
open Trace.Physical.Germ WilsonCapturedPrimaryReading
def depth (d target : ℕ) := target+WilsonCapturedPrimaryEngineering.loss d 0 0

variable {G : Gauge} (R : Run G) (simple : G.Simple) {m i N per k d : ℕ}
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
local notation "F" => R.family.labels.level d
local notation "S" => R.family.localSection d
local notation "Y" => R.family.params
local notation "μ" => (R.family.path.levels.params i).columns
local notation "incomingAt" => LocalComparison.actualPush R.family N per i (physical fired)

local notation "debt" => (fun (ε:ℝ) (p:ℕ)=>(8*Ω^P.op.count)*P.rent+ε*g^p)
local notation "B" => ((2:ℝ)^(order+shelf+2)+4)
local notation "shine" => (fun (q:ℕ)=>βhat^(-(q:ℝ)))
local notation "M" => (fun (α:ℝ)=>WilsonFullFaceSignedPower.constants (S) (Y) α B)

include course cut in
theorem original (gradeCap : (∑j,ages j) ≤ 14) (way : WayStation R.kit) (station : WilsonCenteredCaptureClock.first R simple ≤ i)
    (sec : R.t d ≤ i)
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
    (nodeOrder : WilsonCapturedPrimaryPaid.grade (depth d target) d 1 +(loss+6)≤q) (funded : debt ε p ≤ K*g^q)
    (saved : (eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple q)).choose ≤ i)
    (healthy : 1≤(R.family.path.levels.budget i).supportExponent)
    (wrapped : (eventually_atTop.mp (Trace.Physical.GermGraph.cut_flat R.family simple 0)).choose ≤ i)
    (panelDate : (eventually_atTop.mp (WilsonCapturedPrimaryOnRun.readouts R simple (F) (Y) (S)
      (depth d target) 0 1 le_rfl)).choose ≤ i)
    (tariffDate : (eventually_atTop.mp (WilsonCapturedPrimaryTariff.original R simple d d target 0 0 slow)).choose ≤ i) :
    let tape:=AllOrder.Floe.Step.tape (Burn.horizon k+2)
    let issued:=Air.craft student (fun z=>(student z).paint fired) ages (π i) tape
    let nominal:=fun U=>Poly.pass (Integral.markedLog g U issued)
    let R₀ := |M α| * wallet * (K+4^q+1)
    let A₀ := 192*(Fintype.card (Multi.parts (J)).Mode:ℝ)*wallet*K
    let wrap := WilsonCapturedPrimaryCoreBill.wrapFee (F) (Y)
    let I := WilsonCapturedPrimaryDecoder.invoice (F) (Y) d
    let fieldFee := 2*I*(A₀+(4*wrap+1)*R₀)+wrap*R₀
    ∃ h : Coefficient (F) ((C).side i per), h.Format y (Y) (Ψ i) ∧
      h.remBound y (Ψ i) κ (R₀*g^target) ∧
      (∀ U:configuration, h.density y (S) (Ψ i) U = take c (incomingAt U) -
        ((Ψ i).eval U:ℂ)*take c (nominal U)) ∧
      (F).coeffSize (projection (F) (Y) (Ψ i).p.threshold y h) ≤ fieldFee*g^target ∧
      (F).coeffSize h.x ≤ fieldFee*g^target := by
  intro tape issued nominal R₀ A₀ wrap I fieldFee
  obtain ⟨h,fmt,money,field,projectionPaid,storedPaid⟩:=WilsonGeometricSignedMeasured.original
    R simple cut hk D bank π Γ Ψ course books hi ahead order shelf seats actors pieces ages physical P fired
    gradeCap way station sec slow ready early late pass hospital narrow load p q force deep aged positive opened small c y Z center homes_in
    rad near radius box α strength loss wallet K bought target surplus nodeOrder funded saved healthy wrapped panelDate tariffDate
  refine ⟨h,fmt,money,?_,projectionPaid,storedPaid⟩
  intro U
  exact (field U).trans (congrArg (fun l=>take c (incomingAt U)-((Ψ i).eval U:ℂ)*take c (Poly.pass l))
    (WilsonReceivedAxialFiling.nominal (R:=R) (hk:=hk) (P:=P) (course:=course) (cut:=cut) (x:=fired) (U:=U)))
end YM.Integration.WilsonGeometricSignedCoveredReturn
