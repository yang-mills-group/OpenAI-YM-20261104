import YM.Integration.WilsonMixedTestTableau
import YM.Integration.WilsonOriginalMixedStampedFinite
import YM.Integration.WilsonCoherentMayerSecondFaceTest

/-! Price the actual product test space on which the next physical marked step hears the old and fresh faces. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMixedTestTableau
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Multi Exterior Source Labels LocalComparison ComparisonDensity.Address Comparison.Density.RenderM MergeProof.Accent FVA1
open QuadraticLocal.Rebirth ConnectedActivityE6 FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders WilsonOriginalProjectedCurvatureSalary WilsonOriginalProjectedCurvaturePassport
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
theorem zero {p ℓ n : ℕ} {h : n ≤ ℓ} (S : ActualRunQlocalNativeTuple.Datum R p ℓ n h V) (v : V) :
    (0 : Pos → ℂ) ∈ WilsonOriginalProjectedCurvatureTableau.actors S v :=
  (Orbit.Bill.zero (U:=ActualRunQlocalNativeTuple.orbit S v)).more zero_le_one

variable {j N per : ℕ} {s₀ s₁ : ℕ} {h₀ : s₀ ≤ j+1+1} {h₁ : s₁ ≤ j+1}
  (S₀ : ActualRunQlocalNativeTuple.Datum R per (j+1+1) s₀ h₀ V) (S₁ : ActualRunQlocalNativeTuple.Datum R per (j+1) s₁ h₁ V)
  (old fresh : Finset V)
local notation "A" => WilsonOriginalProjectedCurvatureTableau.actors S₀
local notation "B" => WilsonOriginalProjectedCurvatureTableau.actors S₁
local notation "left" => WilsonMixedTestTableau.left A B old (zero S₀)
local notation "right" => WilsonMixedTestTableau.right A B fresh (zero S₁)

omit [Fintype V] in
/-- The two independently posed tests enter precisely the original fieldwise projected source. -/
theorem projected (x₀ : Affinity.Wallet (WilsonOriginalProjectedCurvatureTableau.actors S₀))
    (x₁ : Affinity.Wallet (WilsonOriginalProjectedCurvatureTableau.actors S₁)) :
    let test := WilsonMixedTestTableau.pair A B x₀ x₁
    left test = WilsonCoherentMayerSecondFaceTest.projected (ActualRunQlocalNativeTuple.orbit S₀) old x₀ ∧
    right test = WilsonCoherentMayerSecondFaceTest.projected (ActualRunQlocalNativeTuple.orbit S₁) fresh x₁ := by
  exact ⟨rfl, rfl⟩

variable (R) {BMS : MS.Local.Physical.Deck G} (freshQ : MS.Land.Prescription BMS)
  (u : V → MS.Rake.Label BMS) (η : ℝ) (orders extra : V → ℕ) (sep : Disjoint old fresh)
  {m k : ℕ} (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  {φ : ℕ → ℕ} (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (Q : D.Tab R.rolls) (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ l, RG.Rep G (R.family.side l per))
  (books : Mentor.Offices.Books D R.rolls Q φ) (floor : m ≤ j)
  (op : Mentor.Opportunity (R.alloy.B.a.clock.J (j+1+1)) (R.alloy.B.a.clock.J (j+1)))
  (lesson : Lesson (N:=N) R hk D Q π Γ (floor.trans (Nat.le_succ j))) (ahead : Mentor.Forecast D R.rolls Q φ books)
  {ι : Type} {P : Earn.Passport (R.family.side (j+1+1) per) V}
  (M : ι → Row P (Stock.census V) G (Affinity.Wallet (WilsonOriginalProjectedCurvatureTableau.actors S₀)))
  (w : V → ℝ) (grades : V → ℕ) (order shelf : ℕ)
  (voter : Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1+1)))
    order op.count op.stage k (R.alloy.B.a.clock.J (j+1))) (cost : ℝ) {a b : Type}
  (Z : Tint.Incoming P (Ψ (j+1+1)) (Affinity.Wallet (WilsonOriginalProjectedCurvatureTableau.actors S₀)) a (Stock.census V))
  (rent : ℝ) (Y : Tint.Incoming (P.coarser (R.family.path.levels.clock.op (j+1) per).ratio)
    (Ψ (j+1)) (Affinity.Wallet (WilsonOriginalProjectedCurvatureTableau.actors S₀)) b (Stock.census V))
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
local notation "t₀" => (fun v => (WilsonOriginalProjectedCurvatureTableau.nulls S₀ v).restrictScalars ℝ)
local notation "t₁" => (fun v => (WilsonOriginalProjectedCurvatureTableau.nulls S₁ v).restrictScalars ℝ)
local notation "received" => WilsonOriginalMixedStampedFinite.Returned R D hk Q π Γ Ψ books floor op lesson ahead
  A M w grades order shelf voter cost t₀ Z rent Y

theorem measured (returned : received) :
    let M₁ := Oak.student (n:=per) R hk D Q π Γ books (floor.trans (Nat.le_succ j)) op lesson ahead A M order voter
    let stamp := Mutation.stamp M₁ (Γ (j+1)) (Oak.grade0 R hk D Q π Γ (floor.trans (Nat.le_succ j)) lesson) (Burn.horizon k+2) order
    let birth := WilsonOriginalProjectedCurvatureLamps.cohort freshQ S₁ u η orders N σ extra
    Tableau (WilsonMixedTestTableau.pieces t₀ t₁) (WilsonMixedTestTableau.actors A B)
      (WilsonMixedFaceLog.routed stamp birth old fresh sep left right) := by
  intro M₁ stamp birth
  unfold WilsonOriginalMixedStampedFinite.Returned at returned
  exact WilsonMixedTestTableau.original A B t₀ t₁ stamp birth old fresh sep (zero S₀) (zero S₁)
    (Mutation.fidelity _ _ _ _ _ _ _ returned.school)
    (WilsonOriginalProjectedCurvatureTableau.real S₁ freshQ u η orders N σ extra)

end YM.Integration.WilsonOriginalMixedTestTableau
