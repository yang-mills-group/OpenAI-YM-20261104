import YM.Integration.WilsonThermometerSubmittedMaterial
import YM.Integration.WilsonPositionProgramVacuumReceipt
import YM.Integration.WilsonPositionProgramWholeBirth

/-! The registered finite thermometer's first deposited field as the original
position-program coefficients on the same forest, real held links and regulator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFirstDeposit
open Function Finset RG Lattice Wilson Marker Multi
open PhysicalNext PhysicalNext.Repeat Legato Next.Scheduling Next.Scheduling.Clock
open Push Input Org Precision Tree Exterior Next.SectorChange AnalyticBridge VerifiedReset ConnectedActivityE6
open Comparison.RG02 Comparison.RG02.Cumulants AllOrder AllOrder.Transit WheelP AllOrder.Floe
open AllOrder.Floe.Step PlanV QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Extra.Iteration
open RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Kick RegulatorIR.FVAAlt2.Booth WilsonThermometerProgramSubmittedWords
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {i m h : ℕ} (per : ℕ)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
    (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (enrolled : PlanV.Path D R.alloy Q h (i+1) m π Γ)
    {V T : Type} [Fintype V] [LinearOrder V] (d : V → ℕ) {base : Side} (o : V → Site base)
local notation "fine" => R.family.side (i+1) per
local notation "coarse" => R.family.side i per
local notation "K" => (RunFormalChain.fromRun R).step (i+1) i per (Nat.lt_succ_self i)
local notation "S" => R.family.path.levels.clock.op i per
local notation "users" => Stock.census V
local notation "single" => Stock.census Unit
variable (mult : base.val ∣ (R.family.side (i+1) per).val) (g τ : ℝ) (v : (j:V) → R.family.label (d j)) (t:V → T → ℂ)
    (x:T) (e : (Stock.census V).Mode)
local notation "J" => Choice R d base (fine) e.val
local notation "d₁" => (fun j : ↥e.val => d j.val)
local notation "stars" q => coords R d o mult e.val q
local notation "v₁" q => axis R d e.val q
local notation "B" q => Boot.scout R (live R d e.val q) (d₁) (v₁ q) (stars q)
local notation "tag₁" => Stock.census ↥e.val
local notation "face" q => (⟨live R d e.val q, mem_univ _⟩ : (tag₁).Mode)
local notation "T" q => Boot.ink (single) () R.family.path (i+1) per (B q)
local notation "W" => WilsonThermometerNumericalBank.bank R d o g τ v t mult x (π (i+1)) (tape (h+2))
local notation "C" q => WilsonThermometerSubmittedMaterial.catalog R d o mult e (π (i+1)) (tape (h+2)) q
local notation "wt" q => (∏ j : ↥e.val, dose R d g τ v t x j.val (q j).2)

private lemma only (y : Hot (Stock.census Unit)) : y=(Arm.pub () : Hot (Stock.census Unit)) := by
  apply Subtype.ext
  apply Subtype.ext
  obtain ⟨a,ha⟩ := y.property
  cases a
  ext j
  cases j
  exact iff_of_true ha (mem_singleton_self ())

private lemma book_word (q : J) :
    QuadraticLocal.Fk.grant (π (i+1)) (tape (h+2)) (T q) = (C q) := by
  unfold WilsonThermometerSubmittedMaterial.catalog QuadraticLocal.Fk.grant
  congr 1
  all_goals
    funext a
    have ha : ∃ k : Unit, (single).fire k = a.val := ⟨(),congrArg Subtype.val (only a).symm⟩
    simp only [Boot.ink, Bare.Signals.flare, dif_pos ha, if_pos (only a)]

include enrolled in
/-- The entire held output is expressed by FVA's native position programme on the
actual selected bare step, including the continuous scalar part of every occupied sector. -/
theorem original (archive : Extension.UV.Archive R.alloy.B) (active : m ≤ i + 1)
    (σ : ℝ) (positive : ∀ j, 0 < d j) (w : V → ℝ) {rent : ℝ} {order slots shelf : ℕ}
    (fleet : Scene.Armada (WilsonOriginalStarGradedScene.words R d o σ g τ v t positive)
      w d σ rent order slots shelf) (rate : 0 < σ)
    (F : Forest (S).ratio) (tag : (S).Choices) (A : fieldDir G coarse 1)
    (D₀ : BudgetPoint) (p : ℕ) (inside : p ≤ h + 2) :
    ∀ k ≤ p, Laplace.detail (Order.ratio (Bulk.Fk (K) F tag (W) A p)) e k =
      ∑ q : J, (wt q) * LocalFormal.runCoefficients R
        (YM.FVAAlt2.Block.ticket R i per (tag₁) (wrap (fine) ∘ (stars q)) (d₁) (v₁ q) F tag A)
          p k (face q) := by
  have legal := WilsonPositionProgramVacuumReceipt.legal R D Q π Γ enrolled active
  have first := WilsonThermometerSubmittedMaterial.registered R d o mult e g τ v t x
    (π (i+1)) (tape (h+2)) (K) F tag A D₀ p legal σ positive w fleet rate
  intro k hk
  rw [first k hk]
  refine sum_congr rfl fun q _ => congrArg ((wt q) * ·) ?_
  rw [← book_word R per π d o mult e q]
  have vac := WilsonPositionProgramVacuumReceipt.original R D Q π Γ enrolled archive active (T q)
    (K) F tag A p inside
  rw [←vac]
  exact (WilsonPositionProgramWholeBirth.original R i per (tag₁) (single) (face q) () (d₁)
    (v₁ q) (stars q) F tag A p k hk).symm

end YM.Integration.WilsonThermometerPositionFirstDeposit
