import YM.Integration.WilsonThermometerFundedJoinCells
import YM.Integration.WilsonThermometerOfferedStep

/-! Exact deposited seven-face panel on each actual filed date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerFundedTrail
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
    (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
    (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
    {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
    (ahead : Mentor.Forecast D R.rolls Q φ books)
    (order shelf seats : ℕ) (mb : m ≤ b) (o : Positions (Fin 3) (R.family.side (b+1) per))
local notation "ages" => (fun v : Fin 3 => (grade v).val)
local notation "panel" => WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self b) o
variable (P₀ : WilsonOriginalReceivedChain.Post (N:=b+1) R hk D Q π Γ Ψ books ahead disks sectors (fun v : Fin 3 => (grade v).val) order shelf seats b mb (WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self b) o))
    {i : ℕ} {floor : m ≤ i}
    {y : Wallet disks → Config G (R.family.side (i+1) per) → Poly (Stock.census (Fin 3))}
    {P : WilsonOriginalReceivedChain.Post (N:=b+1) R hk D Q π Γ Ψ books ahead disks sectors ages
      order shelf seats i floor y}
    (chain : Trail R hk D Q π Γ Ψ books ahead disks sectors ages order shelf seats mb (WilsonThermometerCourseHearing.offered R A simple (Nat.lt_succ_self b) o) P₀ i floor y P)

include chain in
theorem original (ref : ∀ v : Fin 3, R.family.ref (grade v) ≤ b+1) :
    ∃ live : i < b+1, y = WilsonThermometerCourseHearing.offered R A simple live o := by
  induction chain with
  | start => exact ⟨Nat.lt_succ_self b, rfl⟩
  | @step j on prev U L before filed factor one paid wage ih =>
    obtain ⟨upper,same⟩ := ih
    refine ⟨Nat.lt_of_succ_lt upper,?_⟩
    rw [same]
    exact WilsonThermometerOfferedStep.original R A simple upper o ref

include chain in
theorem density (ref : ∀ v : Fin 3, R.family.ref (grade v) ≤ b+1) :
    ∃ live : i < b+1, ∀ x : Wallet disks,
      (Tint.Patrol.picture P.model P.input).density x = WilsonThermometerCourseHearing.offered R A simple live o x := by
  obtain ⟨live,source⟩ := original R simple A hk D Q π Γ Ψ books ahead order shelf seats mb o P₀ chain ref
  exact ⟨live,fun x => (P.represented x).trans (congrFun source x)⟩

end YM.Integration.WilsonThermometerFundedTrail
