import YM.Integration.WilsonOriginalReceivedPost
import YM.Integration.WilsonOriginalFiledSuccessStory
import YM.QuadraticLocal.Class.Registration

/-! Replant the actual paid analytic roster alone on the same measured vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshIssuedIntake
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org 
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (floor : m ≤ i)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))

local notation "post" F:max => WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead
  actors pieces grades order shelf seats i floor F
variable (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead
  actors pieces grades order shelf seats i floor physical)
local instance : Countable P.modelIndex := P.modelCount
local notation "fine" => Ψ (i+1)
local notation "gf" => Coat.gStep (fine).beta
local notation "κ" => forcedDivisor R.family (i+1)
local notation "βhat" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "fresh" => (fun (x : Wallet actors) (U : Config G (R.family.side (i+1) per)) =>
  ((fine).eval U : ℂ) • Poly.pass (Spill.Foundry.uncut P.model gf x U))
local notation "pupil" S:max => Oak.student (n:=per) R hk D Q π Γ books floor (S).op (S).lesson ahead
  actors (S).model order (S).voter

include course in
/-- Start a distinct physical insertion of the *same* registered analytic word, at any
reached date.  The true quiet vacuum is retained, including the partners of every mask slip.
The input regular difference has price zero.  The reported rent can therefore be chosen
after the original model, voter, widths, and their salary have been filed. -/
theorem original (simple : G.Simple) (cut : i<N) (scroll : VowsR.LawScroll G φ)
    (chamber : VowsR.Chamber scroll R.kit D Q books)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (warm : Spill.Raffle.Warm G D R.alloy.delay φ)
    (top : Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
    (fits : order ≤ Burn.horizon k+1) (load : seats ≤ Burn.horizon k+2)
    (packed : order+shelf ≤ Burn.horizon k+2)
    (d : ℕ) (space : Sycamore.Boot.need d (⟨order,seats,shelf,load,fits,packed⟩ : Syl.School k)
      ≤ R.alloy.B.a.clock.J (i+1))
    (test : Wallet actors) (τ : ℝ) (positive : 0<τ) (small : τ≤1) :
    ∃ L : post fresh, L.op=P.op ∧ L.lesson=P.lesson ∧ L.passport=P.passport ∧
      L.modelIndex=P.modelIndex ∧ HEq L.model P.model ∧ L.w=P.w ∧ L.cost=P.cost ∧ L.rent=τ ∧
      (∀ (a : ℝ) (b : ℕ), L.input.old.Paid P.w b a 0) ∧
      L.input.hard.Paid P.w (fine).p.B (fine).p.supportExponent (κ * βhat ^ (-(d:ℝ))) ∧
      (∀ x U, Spill.Foundry.uncut (pupil L) gf x U = Spill.Foundry.uncut (pupil P) gf x U) ∧
      ∀ g x U, Integral.markedLog g U (Air.craft (pupil L) (fun j=>((pupil L) j).paint x)
        grades (π i) (AllOrder.Floe.Step.tape (Burn.horizon k+2))) =
        Integral.markedLog g U (Air.craft (pupil P) (fun j=>((pupil P) j).paint x)
          grades (π i) (AllOrder.Floe.Step.tape (Burn.horizon k+2))) := by
  let school : Syl.School k := ⟨order,seats,shelf,load,fits,packed⟩
  have unit : P.cost ≤ 1 := P.affordable.trans (inv_le_one_of_one_le₀ P.issued.Waffle.cool)
  have stock : Scene.Armada P.model P.w grades
      (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) 1
      school.order school.pieces school.horizon := by
    change Scene.Armada _ _ _ _ 1 order seats shelf
    simpa only [P.capacity] using P.salary.higher unit
  obtain ⟨Z,entry⟩ := Sycamore.Boot.launching R hk D Q π Γ Ψ course scroll books chamber
    (floor.trans i.le_succ) cut actors pieces P.w grades school P.model stock P.tests warm top d space
  have forced : Z.hard.Paid P.w (fine).p.B (fine).p.supportExponent κ := by
    apply Hard.mono _ entry.crown
    have one : 1 ≤ βhat := (R.alloy.B.a.fits.delayed (i+1)).le
    exact mul_le_of_le_one_right (Graces.glyphBound R.alloy.B.a (i+1)).1.le
      (Real.rpow_le_one_of_one_le_of_nonpos one (neg_nonpos.mpr (Nat.cast_nonneg _)))
  have weak := Lamps.loan_monotone _ (Spill.Foundry.empty_lit (fine) Z
      (fine).p.supportExponent (fine).p.B (w:=P.w)) positive.le
  have cal := Classical.choice (Oak.agrees R hk D Q π Γ Ψ course floor cut P.lesson)
  have wide : shelf ≤ R.alloy.B.a.clock.J i :=
    (Nat.le_add_left _ _).trans (packed.trans (hk.trans (R.alloy.B.a.fits.mono floor)))
  obtain ⟨J,count,out,story⟩ := Oak.Buffered.arrive R simple hk D Q π Γ Ψ course scroll books chamber
    floor cut P.op P.lesson cal ahead hospital actors pieces P.model Z P.w grades order shelf P.voter τ P.cost
    (P.capacity.trans_le load) wide P.salary P.tests test entry.clothes.seeds entry.clothes.supplementary
    weak (Hard.mono _ forced (Graces.glyphBound R.alloy.B.a (i+1)).2) unit positive small
  let L : post fresh := {P with
    inputIndex := Empty
    input := Z
    outputIndex := J
    outputCount := count
    output := out
    rent := τ
    active := positive
    small := small
    oldTests := entry.clothes.seeds
    hardTests := entry.clothes.supplementary
    regular := Lamps.loan_monotone _ (Spill.Foundry.empty_lit (fine) Z _ _ (w:=P.w)) positive.le
    forced := forced
    represented := fun x => funext (fun U => (entry.face x U).2.2)
    issued := story}
  exact ⟨L,rfl,rfl,rfl,rfl,HEq.rfl,rfl,rfl,rfl,
    fun a b => Spill.Foundry.empty_lit (fine) Z a b,entry.crown,(fun _ _ => rfl),fun _ _ _ => rfl⟩

end YM.Integration.WilsonOlderFreshIssuedIntake
