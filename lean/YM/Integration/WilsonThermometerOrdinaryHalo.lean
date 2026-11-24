import YM.Integration.WilsonThermometerOrdinaryPole
import YM.Integration.WilsonPlantedOrdinaryHalo
import YM.Integration.WilsonCenteredReporterClock
import YM.Integration.WilsonMarkedFixedPoleGross
import YM.Integration.WilsonReceivedSourceGross
import YM.Integration.WilsonCenteredCaptureClock
import YM.Integration.WilsonThermometerOriginalCylinder

/-! The finite student's ordinary thermometer, with its disconnected
products, is freshly filed in the original Wilson history at this date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerOrdinaryHalo
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
open WilsonThermometerCenteredAlgebra WilsonThermometerWeightedCapture
local notation "J" => Stock.census (Fin 3)
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple) {m i N per k : ℕ}
  (cut : i<N) (o : Positions (Fin 3) (R.family.side N per))
  (hk : Burn.horizon k+2    ≤    R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (bank : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls bank φ) (hi : m   ≤   i)
  (ahead : Mentor.Forecast D R.rolls bank φ books) (order shelf seats : ℕ)
local notation "ages" => (fun j:Fin 3=>(WilsonPositionThermometerGradedSource.grade j).val)
local notation "actual" => offered R A simple cut o
variable (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D bank π Γ Ψ books ahead disks sectors ages
  order shelf seats i hi (offered R A simple cut o))
local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D bank π Γ books hi P.op P.lesson ahead disks
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D bank π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D bank π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "gauge" => (Tint.Patrol.report student P.output oldG)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "width" => ((Ψ i).p.supportExponent+1+1)
local notation "modelFee" => Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count width (fig).limitC G
local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "configuration" => Config G (R.family.side i per)
local notation "value" => LocalComparison.actualPush R.family N per i


local notation "C" => R.family
local notation "F" => R.family.labels.level 0
local notation "S" => R.family.localSection 0
local notation "Y" => R.family.params
local notation "μ" => (R.family.path.levels.params i).columns
local notation "rep" => R.family.path.rep N per i
local notation "cash" => modelFee*((fig).produce (sheet).ratio.count*P.cost)
local notation "raw" => (((2:ℝ)^(order+shelf+1)/(oldG)^15)*cash)
local notation "g" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "rel" => R.alloy.B.a.clock.forcedAllowance i
private abbrev rowsOf {G : Gauge} {n : Side} {V X I : Type} [DecidableEq V] {o : V→Site n} {p : BudgetPoint}
    {R : Census V} (_ : Lamps X I G p o R) := I



include course cut in
theorem original (ref : (C).ref 0  ≤  i) (sec : R.t 0 ≤ i) (station : WilsonCenteredCaptureClock.first R simple  ≤  i)
    (slow : ∀ j, ((R.family.S.block j).val:ℝ)  ≤  Real.log (RG16.Lambda R.family.path.levels j))
    (ready : WilsonReportLampForecast.Ready R.family.path.levels)
    (early : (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (late : (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose  ≤  i)
    (pass : Pass D bank R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls bank R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf   ≤   R.alloy.B.a.clock.J i) (load : P.op.count   ≤   Burn.horizon k+2)
    (s : (J).Mode) (y : Site ((C).side i per)) (Z : Support ((C).side i per)) (center : y∈Z)
    (anchors : ∀j∈s.val,(homes) j∈Z) (rad : ℕ) (near : ∀j∈s.val,separation ((homes) j) y  ≤  rad)
    (radius : rad ≤ (rep).p.B) (box : Z⊆halo (rep).p.B {y}) (α : ℝ) (strength : (rep).p.supportExponent ≤ α) :
    let cost:=WilsonPlantedOrdinary.fare (rep).p Z P.w cash raw rad (S) (Y) μ rel κ s
    let M:=WilsonPlantedOrdinaryHalo.master (S) (Y) α ((2:ℝ)^(order+shelf+2))
    Poly.toll P.w s*cost ≤ M*(g⁻¹)^61 ∧
      WilsonCenteredFiledAtoms.Store rep (S) (Y) y κ cost
        (fun U=>((rep).eval U:ℂ)*(Poly.pass (WilsonRootedKioskOccupiedSlip.bare lamps fired U)).part s) := by
  intro cost M
  have measured:=WilsonThermometerOrdinaryPole.original R A simple cut o hk D bank π Γ Ψ course books hi ahead order shelf seats P
    ref station late pass hospital narrow load s y Z center anchors rad near
  obtain ⟨temp,cap,move,field,live,small,hv,bill,forced⟩:=
    (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose_spec i early N per cut
  have walk:=course.1.walk i hi cut.le
  have proofRep:=R.makes.wilson.represents N per i cut.le
  have shape : (rep).p=R.family.path.levels.budget i:=proofRep.vac
  have same : (rep).p=(Ψ i).p:=proofRep.vac.trans walk.truep.point.symm
  have read :=(WilsonCapturedPrimarySection.original R sec (rep) shape).1
  have e:=P.issued.Waffle
  let ν:=(fig).produce (sheet).ratio.count*P.cost
  have c0 : 0   ≤   P.cost:=budget_nonneg (P.salary.suggests 0)
  have enough : ν   ≤   1:=calc
    _   ≤   Ω*P.cost:=mul_le_mul_of_nonneg_right e.earns c0
    _   ≤   Ω*Ω⁻¹:=mul_le_mul_of_nonneg_left P.affordable e.paysAbove.le
    _ = _:=mul_inv_cancel₀ e.paysAbove.ne'
  have wage: cash   ≤   Ω:=(mul_le_of_le_one_right e.minted.le enough).trans e.quote
  letI : Countable P.modelIndex:=P.modelCount
  letI : Countable (rowsOf (lamps)):=Scene.crewC P.model _ _ (Cruise.funded D R.rolls bank R.alloy φ books P.op
    (Oak.era R hk D bank π Γ hi P.op P.lesson) (R.alloy.B.a.S.oneStep i per).exact_size P.model
    order P.voter P.lesson.entry P.lesson.studied ahead)
  have weighted:=Scene.Armada.paid student P.w ages P.issued.earning (Ψ i).p e.soon
  have α : (Ψ i).p.supportExponent+1+1=(Ψ i).p.supportExponent+2:=by ring
  have wage2 : (lamps).Paid P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) cash := by rw [←α];exact weighted
  have sourced (s:(J).Mode) : (∑v∈s.val,ages v)+1   ≤   15 := by
    have bound:(∑v∈s.val,ages v)  ≤  ∑v:Fin 3,ages v := sum_le_sum_of_subset (subset_univ _)
    have total:(∑v:Fin 3,ages v)=14 := by decide
    omega
  have gross2 : WilsonRootedKioskOccupiedSlip.Gross (lamps) P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) raw := by
    rw [←α]
    exact WilsonMarkedFixedPoleGross.landed student P.w ages (Ψ i).p P.issued.earning e.soon 15 sourced
  constructor
  · apply WilsonPlantedOrdinaryHalo.original (rep).p (S) (Y) Z y P.w s rad temp radius box strength live hv (shape ▸ forced)
      (shape ▸ move) (zero_le_one.trans (R.family.path.levels.params i).columns_ge) field (one_le_pow₀ (by norm_num))
    intro h occ
    simpa only [div_eq_mul_inv,inv_pow,Pert.Asymptotics.regulatorRun,Coat.gStep] using measured.1 h occ
  · exact WilsonPlantedOrdinary.transferred (P:=rep) lamps same fired s y Z center anchors rad near
      P.w P.issued.earning.positive wage2 gross2 (OriginalForcedAddresses.actual_keeper R simple N i per cut.le)
      proofRep.good live hv (shape ▸ bill) (S) (Y) read

end YM.Integration.WilsonThermometerOrdinaryHalo
