import YM.Integration.WilsonReportingAbsoluteInletForecastElection
import YM.Integration.WilsonReportingAbsoluteInletSimultaneous

/-! The before-period inverse book permits different original forest and tag
choices at every cutoff, period and spring of the same complete planted word. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletSchool

open Function Filter Finset Lattice Wilson RG
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open MSbar.Heath WilsonReportingAbsoluteInletForecastMarket
open Pert.Asymptotics FormalBulk08 FormalBulk08.Flat FormalBulk08.Series FormalBulk08.Wine
open MSbar MSbar.Cacao MSbar.Rolling MSbar.Midpoint MSbar.Bakery MSbar.Bakery.Portal
open WilsonConditionalTaylorLabels WilsonConditionalTaylorCourseAttachment WilsonReportingAbsoluteInletForecastBooks
open WilsonReportingAbsoluteInletSimultaneous
open scoped BigOperators Classical

variable {G : Gauge}

abbrev Forests (R : Run G) := ∀ j : ℕ, Lodge (R.family.path.levels.clock.op j 0).patch
abbrev Draws (R : Run G) := ∀ j n, (primary (R.family.path.levels.clock.op j 0).patch
  R.family.path.levels.clock.kernel n).Choices

/-- The submitted gauge and normalization choices can be made separately at each
cutoff, period and spring, before taking the original product. -/
def BoughtAnchor (R : Run G) (a : G.ColorIndex) (κ : ℝ) : Prop :=
  ∀ (wood : ℕ → ℕ → ℕ → Forests R) (tags : ℕ → ℕ → ℕ → Draws R) {c : ℝ}, 1 < c →
    ∀ (P q : ℕ) (b : Roster G),
      let n := WilsonReportingAbsoluteInletCaptured.rank κ P q b+2
      let h := fun N per j => value n (bookH (WilsonConditionalTaylorCourseAttachment.price R a
        (wood N per j) (tags N per j) N per j)) (regulatorRun R.family N per j)
      WilsonReportingAbsoluteInletWholeWord.Receipt R c P q b h

/-- Both inverse polynomials are the inverse action in one original realized scene. -/
theorem same_inverse (R : Run G) (simple : G.Simple) (a : G.ColorIndex) (V : Voice G)
    (money : Terms a V R.kit) (wood₁ wood₂ : Forests R) (tags₁ tags₂ : Draws R)
    (n N per j : ℕ) (step : j<N) (g : ℝ) :
    value n (bookH (WilsonConditionalTaylorCourseAttachment.price R a wood₁ tags₁ N per j)) g =
      value n (bookH (WilsonConditionalTaylorCourseAttachment.price R a wood₂ tags₂ N per j)) g := by
  have issued := (R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  have fortune := townsR R.b R.Q R.T R.t R.stories R.doors issued
  obtain ⟨S,law⟩ := Alto.chosen R.alloy.B simple money.1 fortune N a n per (Nat.zero_le N)
  have sample (v : ℕ) : Alto.Sampled (R.family.side v per) (R.family.path.levels.params v) := money.1.pulse v per
  have read (w : Forests R) (t : Draws R) (e : ℕ) (leq : e ≤ n) :
      PowerSeries.coeff e ((S.action j)⁻¹) = PowerSeries.coeff e (bookH
        (WilsonConditionalTaylorCourseAttachment.price R a w t N per j)) := by
    have field := sceneField R simple a w t law (fun v _ => sample v) (j+1) step (Nat.zero_le _)
    exact ((nextField R simple a w t law j (Nat.zero_le _) step (sample j) field).2).2 e leq
  unfold WilsonReportingAbsoluteInletForecastBooks.value
  apply Finset.sum_congr rfl
  intro e he
  have leq : e ≤ n := by have := Finset.mem_range.mp he; omega
  rw [← read wood₁ tags₁ e leq, ← read wood₂ tags₂ e leq]

theorem anchored (R : Run G) (simple : G.Simple) (a : G.ColorIndex) (V : Voice G)
    (money : Terms a V R.kit) {κ : ℝ} (all : AllAnchors R κ) : BoughtAnchor R a κ := by
  intro wood tags c hc P q b n h
  let fixed := fun N per j => value n (bookH (WilsonConditionalTaylorCourseAttachment.price R a
    (wood 0 0 0) (tags 0 0 0) N per j)) (regulatorRun R.family N per j)
  have invoice := WilsonReportingAbsoluteInletForecastCanonical.original R simple a V money
    (wood 0 0 0) (tags 0 0 0) (WilsonReportingAbsoluteInletCaptured.rank κ P q b)
  apply all hc P q b h
  intro ε ep
  filter_upwards [invoice ε ep] with i paid N per live endp
  have product : (∏ j ∈ Finset.range (N-i), h N per (i+j)) =
      ∏ j ∈ Finset.range (N-i), fixed N per (i+j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have inner : i+j < N := by have := Finset.mem_range.mp hj; omega
    exact same_inverse R simple a V money (wood N per (i+j)) (wood 0 0 0)
      (tags N per (i+j)) (tags 0 0 0) n N per (i+j) inner _
  rw [product]
  exact paid N per live endp

end YM.Integration.WilsonReportingAbsoluteInletSchool
