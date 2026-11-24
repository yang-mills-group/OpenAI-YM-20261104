import YM.Integration.WilsonThermometerPositionFirstDeposit

/-! Full and proper ordinary faces are filed on the finite period before forming
the connected expression or applying its intensive copy normalization. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFirstTable
open Function Filter Finset RG Lattice Wilson Marker Multi
open PhysicalNext PhysicalNext.Repeat Legato Next.Scheduling Next.Scheduling.Clock
open Push Input Org Precision Tree Exterior Next.SectorChange AnalyticBridge VerifiedReset ConnectedActivityE6
open Comparison.RG02 Comparison.RG02.Cumulants AllOrder AllOrder.Transit WheelP AllOrder.Floe
open AllOrder.Floe.Step PlanV QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Extra.Iteration
open RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Kick WilsonThermometerProgramSubmittedWords
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (i per : ℕ) {V T : Type} [Fintype V] [LinearOrder V]
    (d : V → ℕ) {base : Side} (o : V → Site base)
    (mult : base.val ∣ (R.family.side (i+1) per).val)
    (g τ : ℝ) (v : (j:V) → R.family.label (d j)) (t:V → T → ℂ) (x:T)
local notation "fine" => R.family.side (i+1) per
local notation "coarse" => R.family.side i per
local notation "S" => R.family.path.levels.clock.op i per
local notation "J" => Stock.census V
variable (F : Forest (R.family.path.levels.clock.op i per).ratio)
    (tag : (R.family.path.levels.clock.op i per).Choices) (A : fieldDir G (R.family.side i per) 1)
    (p : ℕ)

def filed : Order.PTable (Stock.census V) := PowerSeries.mk fun k =>
  if k ≤ p then Poly.inject (fun e =>
    ∑ q : Choice R d base (fine) e.val,
      (∏ j : ↥e.val, dose R d g τ v t x j.val (q j).2) * LocalFormal.runCoefficients R
        (YM.FVAAlt2.Block.ticket R i per (Stock.census ↥e.val) (wrap (fine) ∘ coords R d o mult e.val q)
          (fun j : ↥e.val => d j.val) (axis R d e.val q) F tag A)
          p k (⟨live R d e.val q, mem_univ _⟩ : (Stock.census ↥e.val).Mode)) else 0

variable {m h : ℕ} (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q : D.Tab R.rolls) (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
    (enrolled : PlanV.Path D R.alloy Q h (i+1) m π Γ)
local notation "K" => (RunFormalChain.fromRun R).step (i+1) i per (Nat.lt_succ_self i)
local notation "W" => WilsonThermometerNumericalBank.bank R d o g τ v t mult x (π (i+1)) (tape (h+2))
local notation "Y" => filed R i per d o mult g τ v t x F tag A p

include enrolled in
/-- Equality of the entire ordinary table, its complete incidence logarithm,
and the scalar vacuum normalization by the same selected inverse. -/
theorem original (archive : Extension.UV.Archive R.alloy.B) (active : m ≤ i + 1)
    (σ : ℝ) (positive : ∀ j, 0 < d j) (w : V → ℝ) {rent : ℝ} {order slots shelf : ℕ}
    (fleet : Scene.Armada (WilsonOriginalStarGradedScene.words R d o σ g τ v t positive)
      w d σ rent order slots shelf) (rate : 0 < σ) (D₀ : BudgetPoint) (inside : p ≤ h + 2) :
    Order.ratio (Bulk.Fk (K) F tag (W) A p) = Order.series (J) p (Y) ∧
      Order.logMarked (Bulk.Fk (K) F tag (W) A p) = Extra.Trajectories.connected (Order.series (J) p (Y)) := by
  let X := Bulk.Fk (K) F tag (W) A p
  have named (e : (J).Mode) :=
    WilsonThermometerPositionFirstDeposit.original R per D Q π Γ enrolled d o mult g τ v t x e
      archive active σ positive w fleet rate F tag A D₀ p inside
  have entry : Order.collect (Order.ratio X) = (Y) := by
    apply PowerSeries.ext
    intro k
    rw [Order.collect_coeff]
    unfold filed
    rw [PowerSeries.coeff_mk]
    by_cases hk : k ≤ p
    · rw [if_pos hk]
      exact Marker.Poly.ext (fun e => named e k hk)
    · simp only [Order.observe,if_neg hk]
  have sym := Order.sym_ratio (Bulk.fk_unit (K) F tag (W) A p) (Bulk.fk_sym (K) F tag (W) A p)
  have equal : Order.ratio X = Order.series (J) p (Y) :=
    entry ▸ (Order.recollect sym).symm
  exact ⟨equal,congrArg Extra.Trajectories.connected equal⟩

end YM.Integration.WilsonThermometerPositionFirstTable
