import YM.Integration.WilsonOriginalReceivedProgram
import YM.Integration.WilsonOriginalCoveredEvolution
import YM.Integration.WilsonReceivedCloseHistory

/-! Identification of all occupied source coefficients along the original, dated Wilson descent. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCoveredTrail
open WilsonReceivedCloseHistory WilsonOriginalReceivedChain WilsonOriginalCopiedHistory
open FVA1Physical.TwoReset
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open scoped BigOperators

variable {G : Gauge} (R : Run G) {m b N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
  (ahead : Mentor.Forecast D R.rolls Q φ books)
  {V : Type} [Fintype V] [DecidableEq V] {X : V → Type}
  [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ) (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))

local notation "carrier" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y

local notation "V₀" => (Stock.census V)
local notation "depth" => Burn.horizon k+2
local notation "tape₀" => AllOrder.Floe.Step.tape depth

variable (P₀ : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats b mb source)
  (x : Wallet actors)
  (top : WilsonOriginalCopiedHistory.Values G (Stock.census V) (R.family.side b per))
  (inlet : b<N) (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  (pass : Pass D Q R.alloy R.kit) (month : Scholar.Month R.rolls D Q R.alloy.delay)
  (fits : order≤Burn.horizon k+1) (shelved : shelf ≤ R.alloy.B.a.clock.J m)
local notation "pupil" lower:max room:max postal:max =>
  Oak.student (i:=lower) (n:=per) R hk D Q π Γ books room (postal).op (postal).lesson ahead
    actors (postal).model order (postal).voter
local notation "prescription" => WilsonOriginalCoveredEvolution.run R inlet π Γ depth order grades top

include inlet course pass month fits shelved in
/-- The initial declared bank is read at every reached date of the very same signed physical Trail. -/
theorem full (entrance : ∀ (grid : Side) (div : (R.family.side b per).val∣grid.val) (d : ℕ),
    d≤order → ∀ z, top grid div d z=peek div (pupil b mb P₀) grades (π (b+1)) tape₀ x d z)
    {i : ℕ} {room : Nat.le m i} {Y : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)}
    {S : carrier i room Y} (T : Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb
      source P₀ i room Y S) :
    ∃ ib : i≤b, ∀ (grid : Side) (div : (R.family.side i per).val∣grid.val) (d : ℕ), d≤order →
      ∀ z, (prescription) i ib grid div d z=peek div (pupil i room S) grades (π (i+1)) tape₀ x d z := by
  induction T with
  | start =>
    refine ⟨le_rfl, ?_⟩
    rw [WilsonOriginalCoveredEvolution.head]
    exact entrance
  | @step j mj y upper lower previous filed factor one paid moved ih =>
    obtain ⟨jb,known⟩ := ih
    have below : j < b := Nat.lt_of_succ_le jb
    have zero := Oak.grade0 R hk D Q π Γ (mj.trans (Nat.le_succ j)) upper.lesson
    refine ⟨below.le, ?_⟩
    intro grid div d hd z
    rw [WilsonOriginalCoveredEvolution.actual R inlet π Γ depth order grades top j below zero]
    exact WilsonOriginalReceivedProgram.successor (R:=R) (hk:=hk) (P:=upper) (L:=lower) (file:=filed)
      (course:=course) (cut:=jb.trans_lt inlet) (pass:=pass) (month:=month) (fits:=fits)
      (narrow:=shelved.trans (R.alloy.B.a.fits.mono (mj.trans (Nat.le_succ j)))) (x:=x)
      (prior:=(prescription) (j+1) jb) (starts:=zero) (known:=known)
      (grid:=grid) (multiple:=div) (d:=d) (hd:=hd) (A₀:=z)

end YM.Integration.WilsonOriginalCoveredTrail
