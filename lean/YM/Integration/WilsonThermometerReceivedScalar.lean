import YM.Integration.WilsonCenteredReceivedAggregate
import YM.Integration.WilsonThermometerOriginalCylinder

/-! The eight actual received faces of the thermometer on one physical
gallery, with its credited signed scalar and the original flat reading. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerReceivedScalar
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
  (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (bank : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls bank φ) (hi : m ≤ i)
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
local notation "oldFee" => Earn.Earnings.hitPrice (fig) G (sheet).ratio.count (Ψ (i+1)).p (Ψ i).p
  (Ω⁻¹*P.cost) (Ω⁻¹*P.rent) (Burn.young (R.alloy.B.a.clock.hatBeta (i+1)) k) oldG
local notation "account" => (Ω^6)⁻¹*(modelFee*((fig).produce (sheet).ratio.count*P.cost)+Ω^P.op.count*oldFee)
local notation "weights" => Stoop.radius P.w (Ω^6)

local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "configuration" => Config G (R.family.side i per)
local notation "value" => LocalComparison.actualPush R.family N per i


local notation "C" => R.family
local notation "F" => R.family.labels.level 0
local notation "S" => R.family.localSection 0
local notation "Y" => R.family.params
local notation "μ" => Next.Foundations.price G (max (Ψ i).p.order (Ψ i).p.power)
local notation "incomingAt" => incoming R A simple cut.le o

include course cut in
theorem original (way : WayStation R.kit) (late : WilsonCenteredCaptureClock.first R simple ≤ i)
    (ref : (C).ref 0 ≤ i) (refs : ∀ j:Fin 3, (C).ref (WilsonPositionThermometerGradedSource.grade j) ≤ N)
    (Q : Poly J) (y : Site ((C).side i per)) (Z : Support ((C).side i per)) (center : y∈Z)
    (homes_in : ∀j:Fin 3,homes j∈Z) (rad : ℕ) (near : ∀j:Fin 3,separation (homes j) y ≤ rad) :
    let fare (s : (J).Mode):=WilsonCenteredGalleryCapture.fare (Ψ i).p (S) (Y) weights s
      (∅:Finset (Fin 3)) (0:Fin 3→ℂ) Z rad account κ (R.alloy.B.a.clock.forcedAllowance i) μ
    ∃ h : Coefficient (F) ((C).side i per), h.Format y (Y) (Ψ i) ∧
      h.remBound y (Ψ i) κ (∑ s,‖weight Q s‖*fare s) ∧
      (∀ U, h.density y (S) (Ψ i) U = (total (incomingAt U) Q).part full) ∧
      (credit C N per 0 (WilsonThermometerLiteralCredit.cut R A o Q) i cut.le=h.density y (S) (Ψ i)) ∧
      (F).coeffSize h.x ≤ testPrice (F)*‖((Ψ i).eval (1:configuration):ℂ)⁻¹*(total (incomingAt 1) Q).part full‖ := by
  intro fare
  have walk:=course.1.walk i hi cut.le
  have same : (Ψ i).p=((C).path.rep N per i).p:=walk.truep.point.trans (R.makes.wilson.represents N per i cut.le).vac.symm
  have read : Readable (Y) (S) (Ψ i).p ((C).side i per) μ := by
    rw [same];exact ActualWilsonPrimaryPreparation.original R 0 N per i ref cut.le
  have hp : 0<κ:=Real.sqrt_pos.mpr (Real.exp_pos _)
  choose H formats paid exacts probes using fun s:(J).Mode=>
    WilsonCenteredReceivedAggregate.original R hk D bank π Γ Ψ course books hi cut ahead disks sectors ages
      order shelf seats actual P way simple late fired s ∅ (fun _=>0) Z y center (fun v _=>homes_in v)
      (by simp) rad (fun v _=>near v) (by simp) (S) (Y) read
  have push : LocalComparison.actualPush (C) N per i (actual fired)=incomingAt := by
    rw [fired_input,WilsonThermometerCourseIntake.step]
  have each (s:(J).Mode) (U:configuration) :
      (H s).density y (S) (Ψ i) U = (incomingAt U).part s := by simpa only [push,sum_empty,sub_zero] using exacts s U
  obtain ⟨form,bill,-,-,field⟩:=deposited R A simple cut.le o (Ψ i) y H Q hp walk.truep.valid fare formats paid each
  let h:=assembled H Q
  refine ⟨h,form,bill,field,(WilsonThermometerLiteralCredit.returned R A simple o Q refs cut.le).trans (funext field).symm,?_⟩
  apply (probe_budget (F)).choose_spec.choose_spec.2 _ _ (norm_nonneg _)
  intro z _
  have rank : z.2.val=0:= Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ z.2.isLt)
  rw [WilsonCenteredDetectorUnit.flatProbe h form read.sound z rank,field]

end YM.Integration.WilsonThermometerReceivedScalar
