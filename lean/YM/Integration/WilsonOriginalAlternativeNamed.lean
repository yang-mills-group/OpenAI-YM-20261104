import YM.Integration.WilsonOriginalAlternativeStamped
import YM.Integration.WilsonOriginalAlternativeVane
import YM.Integration.WilsonThermometerFundedTrail
import YM.Integration.WilsonMeasuredCourseSourceGerm

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeNamed
open Filter Set Finset Wilson Lattice RG Tree Marker Ac QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open FVA1 OriginalForcedAddresses WilsonThermometerCourseIntake
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure Extraction Source ConnectedActivityE6
open WilsonOriginalReceivedChain WilsonReceivedCloseHistory
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonThermometerCourseHearing WilsonSeparatedOriginalThermometerCells
open WilsonOriginalThermometerFineHarvest WilsonOriginalThermometerFineCover WilsonOriginalThermometerFiledCells
open scoped BigOperators Topology ContDiff

variable {G : Gauge} (R : Run G) (simple : G.Simple)
variable (A : Group R.family 6) {m b per k : ℕ}
    (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
    (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
    {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
    (ahead : Mentor.Forecast D R.rolls Q φ books)
    (order shelf seats : ℕ) (mb : m  ≤  b) (o : Positions (Fin 3) (R.family.side (b+1) per))
local notation "ages" => (fun v : Fin 3 => (grade v).val)
local notation "panel" => WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self b) o
variable (P₀ : WilsonOriginalReceivedChain.Post (N:=b+1) R hk D Q π Γ Ψ books ahead disks sectors (fun v : Fin 3 => (grade v).val) order shelf seats b mb (WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self b) o))
    {i : ℕ} {floor : m  ≤  i}
    {y : Wallet disks → Config G (R.family.side (i+1) per) → Poly (Stock.census (Fin 3))}
    {P : WilsonOriginalReceivedChain.Post (N:=b+1) R hk D Q π Γ Ψ books ahead disks sectors ages
      order shelf seats i floor y}
    (chain : Trail R hk D Q π Γ Ψ books ahead disks sectors ages order shelf seats mb (WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self b) o) P₀ i floor y P)


open WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse WilsonOriginalAlternativeExtraction
open WilsonOriginalAlternativePost WilsonOriginalAlternativeHearing
open WilsonPositionThermometerGradedReading
open scoped Classical
local notation "J_" => Stock.census (Fin 3)
local notation "W_" => Ψ (i+1)
local notation "weights_" => wallet J_ P.w

include chain in
private theorem before : i ≤ b := by
  induction chain with
  | start => exact le_rfl
  | @step j on prev U L old filed factor one paid wage ih => exact (Nat.le_succ j).trans ih

include chain in
/-- The chosen Vane and its three physical cutoff fields, on one original trail
before any source substitution, give all eight normalized older readings. -/
theorem original (course:Concourse R.alloy R.kit R.T π Γ m (b+1) per k Ψ)
    (counted:Countable P.inputIndex) (ref:∀a:Fin 3,R.family.ref (grade a) ≤ i+1)
    (v:∀a:Fin 3,R.family.label (grade a)) :
    let cost:=WilsonOriginalAlternativeGuard.rent R (b+1) per (i+1) J_ P.passport.origin ages v P.w (W_).p.supportExponent
    let F:=page R hk D Q π Γ Ψ books ahead disks sectors ages order shelf seats i floor y P v
      (fun x a=>(x a).val)
    ∃ μ:Type,∃ Z:Tint.Incoming (passport P.passport) (W_) (Wallet disks) μ (board J_),
      let L:Gallery (Wallet disks) μ (P.passport.origin∘Prod.fst) (W_) (board J_):=⟨Z.old,Z.hard⟩
      Countable μ ∧ L.Pays weights_ (W_).p.supportExponent (2+cost) (LocalComparison.forcedDivisor R.family (i+1)) ∧
      (∀x h U,Z.hard.hard x h U=inheritAll J_ (P.input.hard.hard x h U)) ∧
      (∀x U,L.density x U=stamped J_ (y x U) (F x U)) ∧
      ∀f (lower:f ≤ i+1) (U:Config G (R.family.side f per)) (s:(J_).Mode),
      let g(c:Fin 3→Port):=held R.family (b+1) per (WilsonOriginalAlternativeHearing.source R.family per J_ L fired c s) lower U
      (∃ before:f ≤ b+1, g (fun _=>0)=
        actualTransport R.family (N:=b+1) (fun Y=>∏a∈s.val,R.family.O (b+1) per
          (A.station.wheel.atCut (b+1,per) (index A (grade a)) ((vector A Finset.univ) a)) (o.origin a) Y) before U) ∧
      g (fun _=>1)=actualTransport R.family (N:=b+1) (fun Y=>∏a∈s.val,F fired Y a) lower U ∧
      (∀j∈s.val,∀c:Fin 3→Port,g (Function.update c j 2)=g (Function.update c j 0)-g (Function.update c j 1)) := by
  have order_date:i ≤ b:=before R simple A hk D Q π Γ Ψ books ahead order shelf seats mb o P₀ chain
  have high:i+1 ≤ b+1:=Nat.succ_le_succ order_date
  have top:∀a:Fin 3,R.family.ref (grade a) ≤ b+1:=fun a=>(ref a).trans high
  obtain ⟨live,field⟩:=WilsonThermometerFundedTrail.original R simple A hk D Q π Γ Ψ books ahead order shelf seats mb o P₀ chain top
  have actual:y fired=incoming R A simple live o:=(congrFun field fired).trans (WilsonThermometerCourseHearing.fired_input R A simple live o)
  have quiet:(Ψ (i+1)).eval=(R.family.path.rep (b+1) per (i+1)).eval:=
    (later R π Γ Ψ course (floor.trans (Nat.le_succ i)) high).view
  let amp (x:Wallet disks) (j:Fin 3):ℂ :=(x j).val
  let F:=page R hk D Q π Γ Ψ books ahead disks sectors ages order shelf seats i floor y P v amp
  letI : Nonempty (Wallet disks):=⟨fired⟩
  obtain ⟨μ,Z,count,pay,hard,allU,raw⟩:=WilsonOriginalAlternativeStamped.original R hk D Q π Γ Ψ books ahead
    disks sectors ages order shelf seats i floor y P counted course high ref v amp (fun x j=>(x j).property)
  refine ⟨μ,Z,count,pay,hard,allU,?_⟩
  intro f lower U s
  obtain ⟨old,trial,_,signed⟩:=raw fired f lower U s
  refine ⟨⟨lower.trans high,?_⟩,?_,signed⟩
  · rw [old,actual]
    exact congrFun (WilsonOriginalAlternativeVane.original R simple (b+1) per A.station
      (fun a:Fin 3=>index A (grade a)) (vector A Finset.univ) o high top s lower) U
  · rw [trial]
    exact congrFun (WilsonOriginalAlternativeVane.planted R (b+1) per high quiet (fun Y=>∏a∈s.val,F fired Y a) lower) U

end YM.Integration.WilsonOriginalAlternativeNamed
