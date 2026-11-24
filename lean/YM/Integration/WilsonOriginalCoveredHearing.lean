import YM.Integration.WilsonOriginalSelfPeriod
import YM.Integration.WilsonOriginalCoveredTrail
import YM.Integration.WilsonOriginalReceivedFoldedTable

/-! The full covered trajectory on the unreplicated original period, in the actual reporting convention. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCoveredHearing
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
/-- All powers and all proper marked subwords are evaluated together on the original torus. -/
theorem evaluated (entrance : ∀ (grid : Side) (div : (R.family.side b per).val∣grid.val) (d : ℕ),
    d≤order → ∀ z, top grid div d z=peek div (pupil b mb P₀) grades (π (b+1)) tape₀ x d z)
    {i : ℕ} {room : Nat.le m i} {Y : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V)}
    {S : carrier i room Y} (T : Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats mb
      source P₀ i room Y S) :
    ∃ ib : i≤b, ∀ (g : ℂ) (z : Stationary.Link G (R.family.side i per)),
      WilsonCoherentMayerWindingGrades.panel order g
        (fun d=>(prescription) i ib _ (dvd_refl _) d z) =
      WilsonCoherentMayerWindingGrades.panel order g (fun d=>
        Air.discharge (Air.craft (pupil i room S) (fun a=>((pupil i room S) a).paint x)
          grades (π i) tape₀) d (Stationary.arm G (R.family.side i per) 1 z)) := by
  classical
  obtain ⟨ib, complete⟩ := WilsonOriginalCoveredTrail.full R hk D Q π Γ Ψ books ahead actors pieces
    grades order shelf seats mb source P₀ x top inlet course pass month fits shelved entrance T
  refine ⟨ib, ?_⟩
  intro g z
  let n := R.family.side i per
  let teacher := pupil i room S
  have staff := Air.license teacher (fun v=>(teacher v).paint x) grades S.w S.issued.earning
    (Poetry.Agenda.stem D φ (Burn.horizon k) (R.alloy.B.a.clock.J i)) (fun v=>S.issued.earning.honor v x)
  apply Finset.sum_congr rfl
  intro d hd
  have hd' : d≤order := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
  have onBase := complete n (dvd_refl _) d hd' z
  have rotate := WilsonOriginalCopiedMarkerLayout.same (dvd_refl n.val) teacher grades
    (π (i+1)) (π i) tape₀ x d z staff
  have field := WilsonOriginalSelfPeriod.original teacher grades (π i) tape₀ x d z staff
  exact congrArg (fun value : Poly (Stock.census V)=>g^d • value) (onBase.trans (rotate.trans field))

end YM.Integration.WilsonOriginalCoveredHearing
