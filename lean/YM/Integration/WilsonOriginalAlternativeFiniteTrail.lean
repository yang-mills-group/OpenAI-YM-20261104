import YM.Integration.WilsonOriginalAlternativeFinitePost
import YM.Integration.WilsonOriginalAlternativeFiniteWallet
import YM.Integration.WilsonOriginalAlternativeNamed

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeFiniteTrail
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

variable {V:Type} [Fintype V] [DecidableEq V]
variable {G:Gauge} (R : Run G)
variable (d:V→ℕ) {m b per k : ℕ} (label:∀j,R.family.book.Ref (d j))
    (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
    (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
    {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
    (ahead : Mentor.Forecast D R.rolls Q φ books)
    (order shelf seats : ℕ) (mb : m  ≤  b) (o : Positions (V) (R.family.side (b+1) per))

variable (P₀ : WilsonOriginalReceivedChain.Post (N:=b+1) R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) (WilsonOriginalAlternativeFiniteSource.sectors (V:=V)) d order shelf seats b mb (WilsonOriginalAlternativeFiniteSource.offer R d (b+1) per label o.origin))
    {i : ℕ} {floor : m  ≤  i}
    {y : Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) → Config G (R.family.side (i+1) per) → Poly (Stock.census (V))}
    {P : WilsonOriginalReceivedChain.Post (N:=b+1) R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) (WilsonOriginalAlternativeFiniteSource.sectors (V:=V)) d
      order shelf seats i floor y}
    (chain : Trail R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) (WilsonOriginalAlternativeFiniteSource.sectors (V:=V)) d order shelf seats mb (WilsonOriginalAlternativeFiniteSource.offer R d (b+1) per label o.origin) P₀ i floor y P)


open WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse WilsonOriginalAlternativeExtraction
open WilsonOriginalAlternativePost WilsonOriginalAlternativeHearing
open WilsonPositionThermometerGradedReading
open scoped Classical
local notation "J_" => Stock.census (V)
local notation "W_" => Ψ (i+1)
local notation "weights_" => wallet J_ P.w

open MergeProof.Accent
include P₀ chain in
theorem source : ∃ live:i+1 ≤ b+1, ∀x, y x=
    gust R.family.path (b+1) per (b+1) (WilsonOriginalAlternativeFiniteSource.offer R d (b+1) per label o.origin x) (i+1) live :=by
  induction chain with
  | start =>
    exact ⟨le_rfl,fun x=>(gust_base R.family.path (b+1) per (b+1) (WilsonOriginalAlternativeFiniteSource.offer R d (b+1) per label o.origin x)).symm⟩
  | @step j on prev U L old filed factor one paid wage ih =>
    obtain ⟨high,prior⟩:=ih
    refine ⟨(Nat.le_succ (j+1)).trans high,fun x=>?_⟩
    change LocalComparison.actualPush R.family (b+1) per (j+1) (prev x)=_
    rw [prior x]
    exact (gust_step _ _ _ _ _ high).symm

include P₀ chain in
/-- Independently nominated physical cutoff fields on one original trail
before any source substitution, give each normalized older reading. -/
theorem original (course:Concourse R.alloy R.kit R.T π Γ m (b+1) per k Ψ)
    (counted:Countable P.inputIndex) (ref:∀a:V,R.family.ref (d a) ≤ i+1)
    (v:∀a:V,R.family.label (d a)) :
    let cost:=WilsonOriginalAlternativeGuard.rent R (b+1) per (i+1) J_ P.passport.origin d v P.w (W_).p.supportExponent
    let F:=page R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) (WilsonOriginalAlternativeFiniteSource.sectors (V:=V)) d order shelf seats i floor y P v
      (fun x a=>(x a).val)
    ∃ μ:Type,∃ Z:Tint.Incoming (passport P.passport) (W_) (Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=V))) μ (board J_),
      let L:Gallery (Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=V))) μ (P.passport.origin∘Prod.fst) (W_) (board J_):=⟨Z.old,Z.hard⟩
      Countable μ ∧ L.Pays weights_ (W_).p.supportExponent (2+cost) (LocalComparison.forcedDivisor R.family (i+1)) ∧
      (∀x h U,Z.hard.hard x h U=inheritAll J_ (P.input.hard.hard x h U)) ∧
      (∀x U,L.density x U=stamped J_ (y x U) (F x U)) ∧
      ∀f (lower:f ≤ i+1) (U:Config G (R.family.side f per)) (s:(J_).Mode),
      let g(c:V→Port):=held R.family (b+1) per (WilsonOriginalAlternativeHearing.source R.family per J_ L (WilsonOriginalAlternativeFiniteSource.fired (V:=V)) c s) lower U
      (∃ before:f ≤ b+1, g (fun _=>0)=
        actualTransport R.family (N:=b+1) (fun Y=>∏a∈s.val,R.family.O (b+1) per
          (label a) (o.origin a) Y) before U) ∧
      g (fun _=>1)=actualTransport R.family (N:=b+1) (fun Y=>∏a∈s.val,F (WilsonOriginalAlternativeFiniteSource.fired (V:=V)) Y a) lower U ∧
      (∀j∈s.val,∀c:V→Port,g (Function.update c j 2)=g (Function.update c j 0)-g (Function.update c j 1)) := by
  obtain ⟨high,field⟩:=source R d label hk D Q π Γ Ψ books ahead order shelf seats mb o P₀ chain
  have quiet:(Ψ (i+1)).eval=(R.family.path.rep (b+1) per (i+1)).eval:=
    (later R π Γ Ψ course (floor.trans (Nat.le_succ i)) high).view
  let amp (x:Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=V))) (j:V):ℂ :=(x j).val
  let F:=page R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) (WilsonOriginalAlternativeFiniteSource.sectors (V:=V)) d order shelf seats i floor y P v amp
  letI : Nonempty (Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=V))):=⟨(WilsonOriginalAlternativeFiniteSource.fired (V:=V))⟩
  obtain ⟨μ,Z,count,pay,hard,allU,raw⟩:=WilsonOriginalAlternativeStamped.original R hk D Q π Γ Ψ books ahead
    (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) (WilsonOriginalAlternativeFiniteSource.sectors (V:=V)) d order shelf seats i floor y P counted course high ref v amp (fun x j=>(x j).property)
  refine ⟨μ,Z,count,pay,hard,allU,?_⟩
  intro f lower U s
  obtain ⟨old,trial,_,signed⟩:=raw (WilsonOriginalAlternativeFiniteSource.fired (V:=V)) f lower U s
  refine ⟨⟨lower.trans high,?_⟩,?_,signed⟩
  · rw [old,field (WilsonOriginalAlternativeFiniteSource.fired (V:=V))]
    have pay:=congrFun (WilsonOriginalAlternativeFiniteSource.actual R d (b+1) per label o.origin (WilsonOriginalAlternativeFiniteSource.fired (V:=V)) high lower s) U
    simpa only [WilsonOriginalAlternativeFiniteSource.probe,WilsonOriginalAlternativeFiniteSource.fired,one_mul] using pay
  · rw [trial]
    exact congrFun (WilsonOriginalAlternativeVane.planted R (b+1) per high quiet (fun Y=>∏a∈s.val,F (WilsonOriginalAlternativeFiniteSource.fired (V:=V)) Y a) lower) U

end YM.Integration.WilsonOriginalAlternativeFiniteTrail
