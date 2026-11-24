import YM.Integration.WilsonReceivedCloseSigned

/-! The enrolled signed comparison at arbitrary points of an original Wilson close interval. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseReadout
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra Source
open FullQLocal FullQLocal.RenderedStep Multi Exterior
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

local notation "read" i:max ib:max => WilsonReceivedCloseHistory.history (N:=N) R actors source i ib
local notation "P" i:max f:max y:max => Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats i f y
local notation "g" => regulatorRun R.family N per
local notation "move" i:max => R.family.path.levels.clock.op i per


/-- The same issued Wilson stations give the physical numerator, the full old vacuum denominator
and the measured reset used by the finite independent block. -/
def Paid (P₀ : P b mb source) (top : b < N) (s : (Stock.census V).Mode)
    (span : ℕ) (H angleCap : ℝ) (width : V → ℝ) (bound : ℝ) : Prop :=
  ∀ i (ib : i ≤ b) (mi : m ≤ i), ∃ L : P i mi (read i ib),
      WilsonReceivedCloseHistory.Trail R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
        mb source P₀ i mi (read i ib) L ∧
      ∀ (x : Wallet actors) (F : Forest (move i).ratio) (tag : (move i).Choices)
        (A : Stationary.Link G (R.family.side i per)) (z : ℝ),
        let B := R.family.path.levels.budget i
        let angle := Stationary.arm G (R.family.side i per) 1 A
        |z| ≤ |H| * (Real.log (R.family.path.levels.clock.hatBeta i))^span*((B.B:ℝ)^2*B.threshold)/(g (i+1)) →
        (∀ e, ‖Exterior.collect G angle e‖ ≤ angleCap * |z|) →
        let W := Integral.sample (g (i+1)) angle
        flags (Ψ i).p.threshold W=∅ →
        let actual := Order.logTo (Fintype.card V) ((((Ψ i).eval W:ℂ)⁻¹) •
          LocalComparison.actualPush R.family N per i ((read i ib) x) W)
        let bank := Air.craft L.model (fun j => (L.model j).paint x) grades (π (i+1)) (AllOrder.Floe.Step.tape (Burn.horizon k+2))
        let step := (RunFormalChain.fromRun R).step N i per (ib.trans_lt top)
        let value := Order.value (g (i+1):ℂ) (Order.logMarked (Bulk.Fk step F tag bank angle order))
        Poly.toll width s*‖(actual-value).part s‖ ≤ bound

/-- Changing to the original physical source radii after hearing keeps exactly the same filed stations. -/
theorem reprice (P₀ : P b mb source) (top : b < N) (s : (Stock.census V).Mode)
    (span : ℕ) (H angleCap : ℝ) {w w' : V → ℝ} {B B' c : ℝ}
    (paid : Paid R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source P₀ top s span H angleCap w B)
    (hn : 0 ≤ c) (h : Poly.toll w' s ≤ c*Poly.toll w s) (total : c*B ≤ B') :
    Paid R hk D Q π Γ Ψ books ahead actors pieces grades order shelf seats
      mb source P₀ top s span H angleCap w' B' := by
  intro i ib mi
  obtain ⟨L,trace,loan⟩ := paid i ib mi
  refine ⟨L,trace,?_⟩
  intro x F tag A z Bdg angle bounded tested W clear
  have bill := loan x F tag A z bounded tested clear
  exact (mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans
    ((le_of_eq (mul_assoc _ _ _)).trans ((mul_le_mul_of_nonneg_left bill hn).trans total))

end YM.Integration.WilsonReceivedCloseReadout
