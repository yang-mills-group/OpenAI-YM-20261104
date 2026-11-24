import YM.Integration.WilsonOriginalAlternativeFiniteTrail

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeFiniteReturn
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

open MergeProof.Accent RG05Readout.Records Extra.Trajectories MeasureTheory
include P₀ chain in
theorem all_faces (x:Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=V))) (s:(J_).Mode) :
    ∃live:i ≤ b+1,(fun U=>(LocalComparison.actualPush R.family (b+1) per i (y x) U).part s)=
      dyes R.family i (b+1) per live (fun Y=>∏j∈s.val,WilsonOriginalAlternativeFiniteSource.probe j x*
        R.family.O (b+1) per (label j) (o.origin j) Y):=by
  obtain ⟨high,field⟩:=WilsonOriginalAlternativeFiniteTrail.source R d label hk D Q π Γ Ψ books ahead
    order shelf seats mb o P₀ chain
  have live:i ≤ b+1:=(Nat.le_succ i).trans high
  refine ⟨live,?_⟩
  let S:=WilsonOriginalAlternativeFiniteSource.offer R d (b+1) per label o.origin x
  have paid:=WilsonOriginalAlternativeFiniteSource.paid R d (b+1) per label o.origin x (le_refl (b+1))
  rw [gust_base] at paid
  have step:LocalComparison.actualPush R.family (b+1) per i (y x)=
      gust R.family.path (b+1) per (b+1) S i live:=by
    rw [field x]
    exact (gust_step _ _ _ _ _ high).symm
  rw [step]
  have parts:=pushpart live S s paid
  have base(U): (S U).part s=(((R.family.path.rep (b+1) per (b+1)).eval U:ℝ):ℂ)*
      (∏j∈s.val,WilsonOriginalAlternativeFiniteSource.probe j x*R.family.O (b+1) per (label j) (o.origin j) U):=by
    change ((MergeProof.Accent.birth (J_) _ _) U).part s=_
    simp only [MergeProof.Accent.birth,MergeProof.Accent.Mach,Poly.part_smul,pass_fire]
  exact parts.trans (congrArg (fun F=>gust R.family.path (b+1) per (b+1) F i live) (funext base))

include P₀ chain in
theorem unary (v:V) :
    ∃live:i ≤ b+1,(fun U=>(LocalComparison.actualPush R.family (b+1) per i (y (WilsonOriginalAlternativeFiniteSource.fired (V:=V))) U).part ((J_).fire v))=
      dyes R.family i (b+1) per live (R.family.O (b+1) per (label v) (o.origin v)):=by
  obtain ⟨high,act⟩:=all_faces R d label hk D Q π Γ Ψ books ahead order shelf seats mb o P₀ chain (WilsonOriginalAlternativeFiniteSource.fired (V:=V)) ((J_).fire v)
  exact ⟨high,by simpa only [show ((J_).fire v).val={v} from rfl,Finset.prod_singleton,
    WilsonOriginalAlternativeFiniteSource.probe,WilsonOriginalAlternativeFiniteSource.fired,one_mul] using act⟩

end YM.Integration.WilsonOriginalAlternativeFiniteReturn
