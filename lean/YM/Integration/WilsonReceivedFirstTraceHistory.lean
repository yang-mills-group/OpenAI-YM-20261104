import YM.Integration.WilsonReceivedFirstTraceStep

/-! A chronological original Wilson descent retaining the genuine first-join output and
independently filed full input at every intermediate date, on the same finite trajectory. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedFirstTrace
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
  (order shelf seats : ℕ)

variable (W : Registration (m:=m) (N:=N) (k:=k) R D Q π Γ Ψ books ahead actors shelf seats)
local notation "carrier" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y



variable (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))
  (P₀ : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats b mb source)
  (c₀ : Countable P₀.inputIndex) (top : b<N) (q : ℕ) (ε : ℝ)

local notation "read" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "g" => regulatorRun R.family N per
local notation "store" U:max count:max cut:max => install R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W U count cut

/-- Every step remembers the counted program as issued, prior to registering its own first
merger. This permits the literal original removed/raised programs to be read at every link. -/
inductive Chain : (i : ℕ) → (floor : m ≤ i) → (cut : i<N) →
    (y : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)) →
    (P : carrier i floor y) → Countable P.inputIndex → Prop
  | start : Chain b mb top source P₀ c₀
  | step {j : ℕ} {floor : m ≤ j} {cut : j+1<N}
      {y : Wallet actors → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census V)}
      {U : carrier (j+1) (floor.trans (Nat.le_succ j)) y} {c : Countable U.inputIndex}
      {L : carrier j floor (fun x => LocalComparison.actualPush R.family N per (j+1) (y x))}
      {h C E : ℝ}
      (previous : Chain (j+1) (floor.trans (Nat.le_succ j)) cut y U c)
      (paid : Receipt R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W floor y U c cut
        (ε*(g (j+2))^q) h C E (ε*(g (j+2))^q) L) :
      Chain j floor (Nat.lt_of_succ_lt cut) _ L paid.counted

local notation "run" => Chain R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W mb source P₀ c₀ top q ε

theorem Chain.trail {i : ℕ} {floor : m ≤ i} {cut : i<N}
    {y : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)}
    {P : carrier i floor y} {c : Countable P.inputIndex} (all : run i floor cut y P c) :
    WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source (store P₀ c₀ top) i floor y (store P c cut) := by
  induction all with
  | start => exact WilsonReceivedCloseHistory.Trail.start
  | step previous paid before =>
    exact WilsonReceivedCloseHistory.Trail.step before
      (filed R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W paid.received paid.counted _)
      _ paid.one paid.price paid.wages

/-- The local cash at a date includes the actual previous signed smooth and compulsory
banks. Its native receipt fixes the next radius before the corresponding rental tolerance. -/
theorem descent (path : PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ)
    (pass : Pass D Q R.alloy R.kit) (month : Scholar.Month R.rolls D Q R.alloy.delay)
    (fits : order ≤ Burn.horizon k+1) (packed : order+shelf ≤ Burn.horizon k+2)
    (deep : 2*q+8 ≤ order) (aged : q+3 ≤ 3*k+2) (ep : 0<ε) (unit : ε ≤ 1)
    (late : WilsonReceivedMeasuredStampPrice.opening R W.simple q order k deep aged ep ≤ m+1)
    (small : ∀ j, m ≤ j → j ≤ N → 0<g j ∧ g j ≤ 1) :
    ∀ i (ib:i ≤ b) (floor:m ≤ i), ∃ P : carrier i floor (read i ib), ∃ c:Countable P.inputIndex,
      run i floor (ib.trans_lt top) (read i ib) P c ∧
      P.rent ≤ P₀.rent+∑j ∈ Ico i b, ε*(g (j+2))^q := by
  intro i ib
  induction ib using Nat.decreasingInduction with
  | self =>
    intro floor
    rw [WilsonReceivedCloseHistory.head (N:=N) R actors source]
    exact ⟨P₀,c₀,Chain.start,by simp⟩
  | of_succ j jb ih =>
    intro floor
    have prev := floor.trans (Nat.le_succ j)
    have cut : j+1<N := lt_of_le_of_lt jb top
    obtain ⟨U,c,above,bill⟩ := ih prev
    let δ := ε*(g (j+2))^q
    have gate := small (j+2) (by omega) (by omega)
    have δp : 0<δ := mul_pos ep (pow_pos gate.1 _)
    have δmax : δ ≤ 1 := mul_le_one₀ unit (pow_nonneg gate.1.le _) (pow_le_one₀ gate.1.le gate.2)
    have room : U.rent+δ ≤ 2 := by linarith only [U.small,δmax]
    obtain ⟨h,C,E,returns⟩ := issued R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W
      floor (read (j+1) jb) U c cut path pass month fits packed q deep aged ep (by omega) room
    obtain ⟨L,paid⟩ := returns δ δp δmax
    have age : L.rent ≤ U.rent+δ := by
      rw [paid.rent]
      apply max_le
      · exact (mul_le_mul_of_nonneg_left paid.available (inv_nonneg.mpr (zero_le_one.trans paid.positive))).trans
          (mul_le_of_le_one_left (U.active.le.trans (le_add_of_nonneg_right δp.le)) (inv_le_one_of_one_le₀ paid.positive))
      · exact le_add_of_nonneg_left U.active.le
    rw [←WilsonReceivedCloseHistory.adjacent (N:=N) R actors source jb]
    refine ⟨L,paid.counted,Chain.step above paid,?_⟩
    rw [←insert_Ico_add_one_left_eq_Ico jb,sum_insert (by simp)]
    dsimp only [δ] at age
    linarith only [age,bill]

end YM.Integration.WilsonReceivedFirstTrace
