import YM.Integration.WilsonThermometerFullSignedRent
import YM.Integration.WilsonGeometricSignedCapture

/-! Every signed face of one received three-source post on its original intake. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGeometricSignedPost
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
local notation "μ" => Next.Foundations.price G (max (Ψ i).p.order (Ψ i).p.power)
local notation "incomingAt" => LocalComparison.actualPush R.family N per i (physical fired)

private abbrev rowsOf {G : Gauge} {n : Side} {V X I : Type} [DecidableEq V] {o : V→Site n} {p : BudgetPoint}
    {U : Census V} (_ : Lamps X I G p o U) := I

include course cut in
theorem original (gradeCap : (∑j,ages j) ≤ 14) (way : WayStation R.kit) (late : WilsonCenteredCaptureClock.first R simple ≤ i)
    (income : ℝ) (read : Readable (Y) (S) (Ψ i).p ((C).side i per) income) (p q : ℕ) (ready : q≤R.alloy.B.a.clock.J i)
    (deep : 2*(p+1)+8 ≤ order) (aged : p+4 ≤ 3*k+2) {ε : ℝ} (positive : 0<ε)
    (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count p order k deep aged positive ≤ i)
    (c : (J).Mode → ℂ) (y : Site ((C).side i per)) (Z : Support ((C).side i per)) (center : y∈Z)
    (homes_in : ∀j:Fin 3,homes j∈Z) (rad : ℕ) (near : ∀j:Fin 3,separation (homes j) y≤rad) :
    let e:=(8*Ω^P.op.count)*P.rent+ε*g^p
    let fare (s:(J).Mode):=WilsonFullFaceSignedCapture.fare (Ψ i).p (S) (Y) Z P.w weights s rad
      cash e raw (βhat^(-(q:ℝ))*κ) ((Ω^6)⁻¹*(cash+e)) rel κ income
    let nominal := fun U=>Poly.pass (WilsonRootedKioskOccupiedSlip.bare lamps fired U)
    ∃ h : Coefficient (F) ((C).side i per),h.Format y (Y) (Ψ i) ∧
      h.remBound y (Ψ i) κ (∑s,‖c s‖*fare s) ∧
      (∀U,h.density y (S) (Ψ i) U=take c (incomingAt U)-
        ((Ψ i).eval U:ℂ)*take c (nominal U)) ∧
      ∀ a : Probe G d, a.2.val = 0 → runProbe (F) a h.x =
        ((Ψ i).eval (1:configuration):ℂ)⁻¹ * (take c (incomingAt 1) -
          ((Ψ i).eval (1:configuration):ℂ)*take c (nominal 1)) := by
  intro e fare nominal
  have walk:=course.1.walk i hi cut.le
  obtain ⟨K⟩:=WilsonCenteredCourseKeeper.original R course i hi cut
  obtain ⟨div,hv,room⟩:=(eventually_atTop.mp (WilsonCenteredCaptureClock.original R simple)).choose_spec i late
  rw [←walk.truep.point] at room
  have inc:=WilsonReceivedInheritedFee.original R hk D bank π Γ Ψ books hi cut P.op P.lesson ahead actors P.model
    P.w ages order shelf P.voter P.cost pieces P.input P.rent P.output P.issued simple p deep aged positive opened
  have aw:=QuadraticLocal.Earn.Scene.Armada.paid student P.w ages P.issued.earning (Ψ i).p P.issued.Waffle.soon
  have alpha : ((Ψ i).p.supportExponent+1+1)=((Ψ i).p.supportExponent+2) := by ring
  have model:(lamps).Paid P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) cash:=by rw [←alpha];exact aw
  have debt : P.output.old.Paid P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) e:=by
    rw [←alpha];exact P.output.old.loan_monotone P.issued.tuition inc
  have gp : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  have epos : 0<e :=add_pos (mul_pos (mul_pos (by norm_num) (pow_pos P.issued.Waffle.paysAbove _)) P.active)
    (mul_pos positive (pow_pos gp _))
  have hw:=P.issued.earning.positive
  have one : 1≤Ω^6:=one_le_pow₀ P.issued.Waffle.cool
  have hs : ∀j,0<weights j := fun j=>div_pos (hw _) (zero_lt_one.trans_le one)
  have soft:=Stoop.tighten P.w _ hw one (Lamps.joinPaid model debt)
  have hard:=P.output.hard.mono P.issued.kept (QuadraticLocal.Advent.force_bill R way π Γ Ψ course hi cut ready)
  have sourced (s:(J).Mode) : (∑v∈s.val,ages v)+1 ≤15 := by
    have bound:(∑v∈s.val,ages v)≤∑v:Fin 3,ages v:=sum_le_sum_of_subset (subset_univ _)
    exact Nat.succ_le_succ (bound.trans gradeCap)
  have gross : WilsonRootedKioskOccupiedSlip.Gross (lamps) P.w (Ψ i).p.B ((Ψ i).p.supportExponent+2) raw:=by
    rw [←alpha]
    exact WilsonMarkedFixedPoleGross.landed student P.w ages (Ψ i).p P.issued.earning P.issued.Waffle.soon 15 sourced
  letI : Countable P.modelIndex:=P.modelCount
  letI : Countable P.outputIndex:=P.outputCount
  letI : Countable (rowsOf (lamps)):=Scene.crewC P.model _ _ (Cruise.funded D R.rolls bank R.alloy φ books P.op
    (Oak.era R hk D bank π Γ hi P.op P.lesson) (R.alloy.B.a.S.oneStep i per).exact_size P.model
    order P.voter P.lesson.entry P.lesson.studied ahead)
  have push : (gauge).density fired = incomingAt :=
    (WilsonOriginalReceivedChain.report R hk D bank π Γ Ψ books ahead actors pieces ages
      order shelf seats i hi physical P fired).symm
  have single (s:(J).Mode) : WilsonCenteredFiledAtoms.Store (Ψ i) (S) (Y) y κ (fare s)
      (fun U=>(incomingAt U).part s-((Ψ i).eval U:ℂ)*(nominal U).part s) :=by
    obtain ⟨h,fmt,bill,field⟩:=WilsonFullFaceSignedCapture.face (ι:=rowsOf (lamps)) (lamps) P.output.old P.output.hard fired s P.w weights
      hw hs epos model debt gross soft hard K walk.truep.valid div hv room (S) (Y) read y Z center
      (fun j _=>homes_in j) rad (fun j _=>near j)
    refine ⟨h,fmt,bill,fun U=>?_⟩
    change h.density y (S) (Ψ i) U=(incomingAt U).part s-((Ψ i).eval U:ℂ)*(nominal U).part s
    rw [←push]
    exact field U
  exact WilsonGeometricSignedCapture.pooled (S) (Y) y div walk.truep.valid read c incomingAt nominal fare single

end YM.Integration.WilsonGeometricSignedPost
