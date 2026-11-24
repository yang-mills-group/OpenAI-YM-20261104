import YM.Integration.WilsonThermometerPositionFilmSeats

/-! The funded original position pupils on the unreplicated forest and every genuine source face. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionOrbitPayout
open Function Finset RG Lattice Wilson Marker Multi
open PhysicalNext PhysicalNext.Repeat Legato Next.Scheduling Next.Scheduling.Clock
open Push Input Org Precision Tree Exterior Next.SectorChange AnalyticBridge VerifiedReset ConnectedActivityE6
open Comparison.RG02 Comparison.RG02.Cumulants AllOrder AllOrder.Transit WheelP AllOrder.Floe
open AllOrder.Floe.Step PlanV QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Extra.Iteration
open RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Kick RegulatorIR.FVAAlt2.Booth WilsonThermometerProgramSubmittedWords
open Comparison.RG02.Symmetry WilsonThermometerOriginalCoveredRows
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
local notation "wt" q => (∏ j : ↥e.val, dose R d g τ v t x j.val (q j).2)

local notation "U" q => Boot.ink (single) () R.family.path (i+1) per (Boot.scout R univ (d₁) (v₁ q) (stars q))
include enrolled in
theorem allGrades (archive : Extension.UV.Archive R.alloy.B) (active : m ≤ i + 1)
    (σ : ℝ) (positive : ∀ j, 0 < d j) (w : V → ℝ) {rent : ℝ} {order slots shelf : ℕ}
    (fleet : Scene.Armada (WilsonOriginalStarGradedScene.words R d o σ g τ v t positive)
      w d σ rent order slots shelf) (rate : 0 < σ)
    (F : Forest (S).ratio) (tag : (S).Choices) (A : fieldDir G coarse 1)
    (D₀ : BudgetPoint) (p : ℕ) (inside : p ≤ h + 2) :
    ∀ k ≤ p, Laplace.detail (Order.ratio (Bulk.Fk (K) F tag (W) A p)) e k =
      ∑ q : J, (wt q) * Orbit.words (K) F tag (U q) p ((single).fire ()) k A := by
  intro k hk
  rw [WilsonThermometerPositionFirstDeposit.original R per D Q π Γ enrolled d o mult g τ v t x e
    archive active σ positive w fleet rate F tag A D₀ p inside k hk]
  refine sum_congr rfl fun q _ => congrArg ((wt q) * ·) ?_
  refine (WilsonPositionProgramWholeBirth.original R i per (tag₁) (single) (face q) () (d₁) (v₁ q) (stars q) F tag A p k hk).trans ?_
  change Laplace.detail (Order.ratio (Bulk.Fk (K) F tag (T q) A p)) ((single).fire ()) k=_
  rw [WilsonThermometerPositionFilmSeats.submitted R d o mult e.val q (single) () (i+1) per]
  exact Comparison.RG02.FVAAlt2.Lyric.logo (Bulk.fk_sym (K) F tag (U q) A p) (Bulk.fk_unit (K) F tag (U q) A p) () hk

include enrolled in
theorem original (archive : Extension.UV.Archive R.alloy.B) (active : m ≤ i + 1)
    (σ : ℝ) (positive : ∀ j, 0 < d j) (w : V → ℝ) {rent : ℝ} {order slots shelf : ℕ}
    (fleet : Scene.Armada (WilsonOriginalStarGradedScene.words R d o σ g τ v t positive)
      w d σ rent order slots shelf) (rate : 0 < σ)
    (F : Forest (S).ratio) (tag : (S).Choices) (A : fieldDir G coarse 1)
    (D₀ : BudgetPoint) (p : ℕ) (inside : p ≤ h + 2) (nonzero:0<p) :
    Laplace.detail (Order.ratio (Bulk.Fk (K) F tag (W) A p)) e 0 =
      ∑ q : J, (wt q) * (Extra.Trajectories.connected (WilsonThermometerOriginalCoveredRows.base (K) F tag (U q) A)).part ((single).fire ()) ∧
    Laplace.detail (Order.ratio (Bulk.Fk (K) F tag (W) A p)) e 1 =
      ∑ q : J, (wt q) * ((first (K) F tag (U q) A) * YM.Primitives.GCC.Anchor.inverseMass (WilsonThermometerOriginalCoveredRows.base (K) F tag (U q) A) -
        Poly.bead (single) ((first (K) F tag (U q) A).part (single).quiet)).part ((single).fire ()) := by
  have bound:=allGrades R per D Q π Γ enrolled d o mult g τ v t x e archive active σ positive w fleet rate F tag A D₀ p inside
  constructor
  · rw [bound 0 (Nat.zero_le _)]
    exact sum_congr rfl fun q _=>congrArg ((wt q)*·) (WilsonThermometerOriginalFilmRows.occupied (K) F tag (U q) p nonzero ((single).fire ()) A).1
  · rw [bound 1 nonzero]
    exact sum_congr rfl fun q _=>congrArg ((wt q)*·) (WilsonThermometerOriginalFilmRows.occupied (K) F tag (U q) p nonzero ((single).fire ()) A).2

end YM.Integration.WilsonThermometerPositionOrbitPayout
