import YM.Integration.WilsonOriginalAlternativeFiniteExchange
import YM.Integration.WilsonOriginalAlternativeTrialBirth
import YM.Integration.WilsonOriginalAlternativeFiniteTrail
import YM.Integration.WilsonOriginalAlternativeTelescope

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialNet
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
local notation "fired_" => (WilsonOriginalAlternativeFiniteSource.fired (V:=V))
open WilsonOriginalAlternativeTelescope

/-- The signed alternatives in the original gallery use the very same guarded fields
that form the new trial. Each charge retains the old filed configuration. -/
def Receipt (v:∀a:V,R.family.label (d a))(z:V→ℂ):Prop:=
    let cost:=WilsonOriginalAlternativeGuard.rent R (b+1) per (i+1) J_ P.passport.origin d (fun a=>z a • v a) P.w (W_).p.supportExponent
    let F:=fun (x:Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=V))) (U:Config G (R.family.side (i+1) per)) (a:V)=>
      (x a).val*WilsonOriginalAlternativeTrialSource.arm R d (b+1) per (i+1) P.passport.origin v z a U
    ∃ μ:Type,∃ Z:Tint.Incoming (passport P.passport) (W_) (Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=V))) μ (board J_),
      let L:Gallery (Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=V))) μ (P.passport.origin∘Prod.fst) (W_) (board J_):=⟨Z.old,Z.hard⟩
      Countable μ ∧ L.Pays weights_ (W_).p.supportExponent (2+cost) (LocalComparison.forcedDivisor R.family (i+1)) ∧
      (∀x h U,Z.hard.hard x h U=inheritAll J_ (P.input.hard.hard x h U)) ∧
      (∀x U,L.density x U=stamped J_ (y x U) (F x U)) ∧
      ∀f (lower:f ≤ i+1) (U:Config G (R.family.side f per)) (s:(J_).Mode),
      ∃ before:f ≤ b+1,
        let D:=charge R.family (N:=b+1) J_ y F fired_ s lower U
        let diff:=actualTransport R.family (N:=b+1) (fun Y=>∏a∈s.val,R.family.O (b+1) per (label a) (o.origin a) Y)
            before U-actualTransport R.family (N:=b+1) (fun Y=>∏a∈s.val,F fired_ Y a) lower U
        (∀l:List V,l.toFinset=s.val → l.Nodup → diff=tally D l) ∧
        (∀fee:V→ℝ,(∀j∈s.val,∀X:Finset V,X⊆s.val → j∉X → ‖D j X‖ ≤ fee j) →
          ‖diff‖ ≤ ∑j∈s.val,fee j)

include P₀ chain in
theorem original (course:Concourse R.alloy R.kit R.T π Γ m (b+1) per k Ψ)
    (counted:Countable P.inputIndex) (ref:∀a:V,R.family.ref (d a) ≤ i+1)
    (v:∀a:V,R.family.label (d a))(z:V→ℂ):
    Receipt R d label hk D Q π Γ Ψ books ahead order shelf seats o (P:=P) v z:=by
  obtain ⟨high,_⟩:=WilsonOriginalAlternativeFiniteTrail.source R d label hk D Q π Γ Ψ books ahead order shelf seats mb o P₀ chain
  have same: (R.family.path.rep (b+1) per (i+1)).p=(Ψ (i+1)).p:=
    (WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course (floor.trans (Nat.le_succ i)) high).1
  let F:=page R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
    (WilsonOriginalAlternativeFiniteSource.sectors (V:=V)) d order shelf seats i floor y P (fun a=>z a • v a) (fun x a=>(x a).val)
  let paid:=fun (x:Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=V))) (U:Config G (R.family.side (i+1) per)) (a:V)=>
    (x a).val*WilsonOriginalAlternativeTrialSource.arm R d (b+1) per (i+1) P.passport.origin v z a U
  have agrees:F=paid:=by
    funext x U a
    change (x a).val*Extra.Histories.part (R.family.localSection (d a)) (P.passport.origin a) (Ψ (i+1)) U (z a • v a)=_
    rw [LinearMap.map_smul,smul_eq_mul]
    simp only [paid,WilsonOriginalAlternativeTrialSource.arm,Extra.Histories.part,LinearMap.coe_mk,AddHom.coe_mk,same]
  have all:=WilsonOriginalAlternativeFiniteExchange.original R d label hk D Q π Γ Ψ books ahead order shelf seats mb o P₀ chain course counted ref (fun a=>z a • v a)
  dsimp only at all
  unfold F at agrees
  rw [agrees] at all
  exact all

end YM.Integration.WilsonOriginalAlternativeTrialNet
end
