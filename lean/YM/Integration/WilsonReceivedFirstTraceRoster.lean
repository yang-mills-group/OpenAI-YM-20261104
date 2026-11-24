import YM.Integration.WilsonReceivedFirstTraceHistory

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




/-- The literal stored Wilson source and its paid post at one date. -/
structure Position (j : ℕ) where
  floor : m≤j
  cut : j<N
  field : Wallet actors → Config G (R.family.side (j+1) per) → Poly (Stock.census V)
  post : carrier j floor field
  counted : Countable post.inputIndex

local notation "place" j:max => Position (m:=m) (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats j
local notation "g" => regulatorRun R.family N per

/-- A stored consecutive pair is exactly the original receipt produced before its
receiving post was registered. The source is pushed on the original measured kernel. -/
inductive Adjacent (q : ℕ) (ε : ℝ) (j : ℕ) : place (j+1) → place j → Prop
  | actual {floor : m≤j} {cut : j+1<N}
      {field : Wallet actors → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census V)}
      {U : carrier (j+1) (floor.trans (Nat.le_succ j)) field} {c : Countable U.inputIndex}
      {L : carrier j floor (fun x=>LocalComparison.actualPush R.family N per (j+1) (field x))}
      {h C E : ℝ}
      (p : Receipt R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W floor field U c cut
        (ε*(g (j+2))^q) h C E (ε*(g (j+2))^q) L) :
      Adjacent q ε j ⟨_,cut,field,U,c⟩ ⟨floor,Nat.lt_of_succ_lt cut,_,L,p.counted⟩

variable (mb : m ≤ b)
  (source : Wallet actors → Config G (R.family.side (b+1) per) → Poly (Stock.census V))
  (P₀ : Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats b mb source)
  (c₀ : Countable P₀.inputIndex) (top : b<N) (q : ℕ) (ε : ℝ)

local notation "read" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib

local notation "store" U:max count:max cut:max => install R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W U count cut


local notation "run" => Chain R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W mb source P₀ c₀ top q ε
local notation "linked" j:max u:max l:max => Adjacent R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W q ε j u l
local notation "initial" => (⟨mb,top,source,P₀,c₀⟩ : place b)

theorem Chain.level {i : ℕ} {floor : m ≤ i} {cut : i < N}
    {field : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)}
    {P : carrier i floor field} {c : Countable P.inputIndex} (chain:run i floor cut field P c) : i≤b := by
  induction chain with
  | start => exact le_rfl
  | step _ _ ih => exact (Nat.le_succ _).trans ih

/-- A single array for every adjacent date, with the literal measured edge and both
original prefixes. The array is selected once, before the date or position is tested. -/
theorem Chain.roster {i : ℕ} {floor : m ≤ i} {cut : i < N}
    {field : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)}
    {P : carrier i floor field} {c : Countable P.inputIndex} (chain:run i floor cut field P c) :
    ∃ f : (j : ℕ) → Option (place j),
      f b=some initial ∧ f i=some (⟨floor,cut,field,P,c⟩ : place i) ∧
      ∀ j,i≤j → j<b → ∃ (U : place (j+1)) (L : place j),
        f (j+1)=some U ∧ f j=some L ∧ linked j U L ∧
        run (j+1) U.floor U.cut U.field U.post U.counted ∧ run j L.floor L.cut L.field L.post L.counted := by
  induction chain with
  | start =>
    let f : (j : ℕ) → Option (place j) := Function.update (fun _=>none) b (some initial)
    refine ⟨f,by simp [f],by simp [f],?_⟩
    intro j bj jb
    exact (not_lt_of_ge bj jb).elim
  | @step j floor cut y U c L h C E prev paid ih =>
    obtain ⟨f,ftop,fup,links⟩ := ih
    let upper : place (j+1) := ⟨_,cut,y,U,c⟩
    let lower : place j := ⟨floor,Nat.lt_of_succ_lt cut,_,L,paid.counted⟩
    let after : (z : ℕ) → Option (place z) := Function.update f j (some lower)
    have jb : j<b := (Nat.lt_succ_self _).trans_le
      (Chain.level R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats W mb source P₀ c₀ top q ε prev)
    refine ⟨after,?_,by simp [after,lower],?_⟩
    · simpa [after,Function.update_of_ne jb.ne'] using ftop
    intro z jz zb
    by_cases here : z=j
    · subst z
      refine ⟨upper,lower,?_,by simp [after],Adjacent.actual paid,prev,Chain.step prev paid⟩
      simpa [upper,after,Function.update_of_ne (Nat.ne_of_gt (Nat.lt_succ_self j))] using fup
    · obtain ⟨U',L',fu,fl,edge,above,below⟩ := links z (by omega) zb
      have next : z+1≠j := by omega
      exact ⟨U',L',by simpa [after,Function.update_of_ne next] using fu,
        by simpa [after,Function.update_of_ne here] using fl,edge,above,below⟩

end YM.Integration.WilsonReceivedFirstTrace
