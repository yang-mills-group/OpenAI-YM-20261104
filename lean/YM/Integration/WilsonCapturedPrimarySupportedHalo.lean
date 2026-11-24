import YM.Integration.WilsonCapturedPrimaryCaptureRoom
import YM.Integration.WilsonCloseCaptureDate
import YM.Integration.WilsonCapturedPrimaryCutoffOath
import YM.Integration.WilsonOriginalThermometerPalette

/-! True compact fine-cell roots enter the original physical capture halo
on the enacted dated course, before either finite regulator is selected. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySupportedHalo
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Pert.Asymptotics Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter
open Extra.Histories Further.PhysicalPeriodLimitF933 Push.AbsoluteSums Planned.GuardedAtom
open scoped Classical BigOperators Topology
open Labels Source Push.Local Next.Foundations Planned.AtomRegular Trace.Physical.Germ
open RG16


open Trace.Physical.GermGraph RG16.Literal MergeProof.East MergeProof.Accent
open FVA1 Cells Extraction Table Climb Trace Trace.Pilot
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonThermometerCourseHearing
open WilsonOriginalThermometerPalette (levels)
open RG12
open WilsonCapturedPrimaryCutoffOath

variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple) {m b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ  →  Layout G) (Γ : ℕ  →  Pace.Coin) (Ψ : ∀ i, RG.Rep G (R.family.side i per))
  {φ : ℕ  →  ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (ahead : Mentor.Forecast D R.rolls Q φ books)
  (order shelf seats : ℕ) (mb : m ≤ b) (top : b<N) (o : Positions (Fin 3) (R.family.side N per))
local notation "head" => offered R A simple top o
local notation "bank" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R disks head i ib
local notation "post" i:max f:max src:max => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead
  disks sectors levels order shelf seats i f src
local notation "trace" S:max i:max mi:max ib:max L:max => WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead
  disks sectors levels order shelf seats mb head S i mi (bank i ib) L
local notation "J" => Stock.census (Fin 3)
local notation "g" => regulatorRun R.family N per
local notation "pred" d:max i:max z:max => projection (R.family.labels.level d) R.family.params (Ψ i).p.threshold 0 z
local notation "move" i:max => R.family.path.levels.clock.op i per
local notation "F" s:max => word R A o s


def date (R : Run G) (r : ℝ) := WilsonCloseCaptureDate.level R.family.S r

include simple in
theorem dated (φ : Test 3) : ∃ t:ℝ,0<t ∧ ∀ r:ℝ,0<r  →  r ≤ t  → 
    ∀ (N per:ℕ) (live:date R r ≤ N) (sites:Fin 3 → Site (R.family.side N per)),
    WilsonSeparatedOriginalThermometerCells.weight φ
      (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (N,per)) sites ≠ 0  → 
    ∀ v, separation ((R.family.S.toDepth live per).parent (sites v)) 0 ≤ (R.family.path.levels.budget (date R r)).B := by
  obtain ⟨M,wallet⟩:=eventually_atTop.mp (WilsonCapturedPrimaryCaptureRoom.capture R simple φ)
  refine ⟨R.family.S.a M,R.family.S.a_pos M,?_⟩
  intro r rp small N per live sites active v
  have valid := small.trans (R.family.S.strictAnti.antitone (Nat.zero_le M))
  have bracket:=WilsonCloseCaptureDate.bracket R.family.S rp valid
  have late:M ≤ date R r := by
    by_contra! early
    have same:=R.family.S.strictAnti.antitone (Nat.succ_le_of_lt early)
    exact (not_lt_of_ge same) (bracket.1.trans_le small)
  exact wallet _ late r ((abs_of_pos rp).le.trans bracket.2) N per live sites active v

theorem original (φ:Test 3) (r:ℝ) (rp:0<r)
    (small:r ≤ (dated R simple φ).choose)
    {source:Wallet disks → Config G (R.family.side (b+1) per) → Poly J} (S:post b mb source)
    {i:ℕ} (stamp:i=date R r) (ib:i ≤ b) {mi:m ≤ i}
    {input:Wallet disks → Config G (R.family.side (i+1) per) → Poly J} {L:post i mi input}
    (traced:WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead disks sectors levels order shelf seats
      mb source S i mi input L)
    (mass:WilsonSeparatedOriginalThermometerCells.weight φ
      (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (b+1,per)) S.passport.origin ≠ 0) :
    let homes:=(L.passport.coarser (move i).ratio).origin
    let B:=(R.family.path.levels.budget i).B
    ∀v, homes v∈halo B {0} ∧ separation (homes v) 0 ≤ B := by
  subst i
  dsimp only
  intro v
  have actual:=WilsonCapturedPrimaryTrailSites.outgoing R hk D Q π Γ Ψ books ahead disks sectors levels
    order shelf seats mb source S ib traced v
  have charge:=(dated R simple φ).choose_spec.2 r rp small (b+1) per (ib.trans (Nat.le_succ _))
    S.passport.origin mass v
  rw [←actual] at charge
  exact ⟨halo_spec.mpr ⟨0,Finset.mem_singleton_self _,by rwa [separation_comm]⟩,charge⟩

end YM.Integration.WilsonCapturedPrimarySupportedHalo
