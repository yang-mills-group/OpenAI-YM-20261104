import YM.Integration.ActualStartupNormalizedQ

/-! One support and regulator independent price for each actual original
Wilson polynomial. The physical test readers and fee polynomials are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSectionPrice
open Function Finset MeasureTheory Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison
open IterationFour IterationFour.Vacuum FullQLocal.RenderedStep
open MergeProof MergeProof.Accent
open scoped Classical BigOperators Topology
variable {G : Gauge}

/-- The coefficient and the original stencil are fixed before all torus sides,
locations and link configurations. -/
theorem uniform {d : ℕ} {F : Frame G d} (S : SectionData F) (v : F.Coeff) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ (n : Side) (z : Site n) (U : Config G n), ‖S.places v z U‖ ≤ a := by
  obtain ⟨b,hb⟩ := (isCompact_range (S.continuous_evaluate v).norm).bddAbove
  exact ⟨max 0 b,le_max_left _ _,fun n z U => (hb ⟨expandAt z U,rfl⟩).trans (le_max_right _ _)⟩

def price {d : ℕ} {F : Frame G d} (S : SectionData F) (v : F.Coeff) : ℝ := (uniform S v).choose

variable {R : Run G} {B : MS.Local.Physical.Deck G}

def column (Q : MS.Land.Prescription B) (u : MS.Rake.Label B) (μ : ℝ) (k : ℕ) : ℝ :=
  ∑ g : MS.Menus.Glyph B u.h, ‖MS.Menus.oil (Q.fees u.h u.item) g k μ‖ *
    price (R.family.localSection g.size) (ActualOriginalDictionary.coordinates R B g.size g.grade g.2.2)

theorem column_nonneg (Q : MS.Land.Prescription B) (u : MS.Rake.Label B) (μ : ℝ) (k : ℕ) :
    0 ≤ column (R:=R) Q u μ k := by
  apply Finset.sum_nonneg
  exact fun g _ => mul_nonneg (norm_nonneg _) (uniform _ _).choose_spec.1

/-- The prescription, including its entire original fee sum, gets one price
before the period and position are chosen. -/
theorem priced (Q : MS.Land.Prescription B) (u : MS.Rake.Label B) (μ : ℝ) (k : ℕ)
    (n : Side) (z : Site n) (U : Config G n) :
    ‖ActualOriginalCalibratedColumns.weightedObservable R B Q u μ n z U k‖ ≤ column (R:=R) Q u μ k := by
  rw [ActualOriginalCalibratedColumns.weighted_observable_original]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((uniform _ _).choose_spec.2 n z U) (norm_nonneg _)

variable {V : Type} {m p n : ℕ} {hn : n ≤ m+1} [DecidableEq V] [Fintype V]

def mode (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p (m+1) n hn V)
    (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (s : (Stock.census V).Mode) : ℝ :=
  ∏ i ∈ s.val, ‖ActualRunQlocalNativeTuple.reader D i (x i)‖ * column (R:=R) Q (u i) μ (orders i)

theorem readout (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p (m+1) n hn V)
    (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (s : (Stock.census V).Mode) (U : Config G (R.family.side (m+1) p)) :
    ‖ActualStartupNormalizedQ.modeObservable Q D u μ orders x s U‖ ≤ mode Q D u μ orders x s := by
  unfold ActualStartupNormalizedQ.modeObservable mode
  rw [norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro i _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (priced Q (u i) μ (orders i) _ _ _) (norm_nonneg _)

end YM.Integration.WilsonSectionPrice
