import YM.Integration.LocalComparisonEnvelope

/-! An auxiliary zero-marked remainder on the original full vacuum and the
original declared layout. No original input coefficient is modified. The
vacuum K rows, admissibility flags and supports remain literally unchanged.
This prepares an already-proved bare factorization; it is not a decomposition
of an arbitrary inherited regular remainder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker Overlay MeasureTheory
open RG3.Held RG3.Forms RG3.Script.Picnic
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
  {R : Census V} {X Y : Type*} {P : Rep G n} {o : V → Site n}

/-- Only the auxiliary remainder's marked coefficients are zeroed. In
particular, no padded row is retagged and the original vacuum is retained. -/
def vacuumRemainder (T : Taste X o P R) : Taste X o P R where
  menu :=
    { origins := T.menu.origins
      rays := T.menu.rays
      branch := T.menu.branch
      marks := T.menu.marks
      global := fun _ _ => 0
      regular := fun _ _ _ => 0
      force := fun _ _ _ _ => 0 }
  root := T.root
  tag := T.tag
  site := T.site
  score := fun _ _ => 0

private theorem zero_left (k : List (Directions G n)) (U : Config G n) :
    leftDerivs (fun _ : Config G n => (0 : ℂ)) k U = 0 := by
  induction k generalizing U with
  | nil => rfl
  | cons A k ih =>
    change deriv (fun t : ℝ => leftDerivs (fun _ : Config G n => (0 : ℂ)) k
      (increment U (t • A))) 0 = 0
    simp only [ih, deriv_const]

private theorem zero_regular (p : BudgetPoint) (s : Support n) :
    p.Regular s (fun _ : Config G n => (0 : ℂ)) := by
  refine ⟨fun _ _ _ => rfl, measurable_const, fun _ _ => rfl,
    fun _ _ => contDiffAt_const, ?_⟩
  intro U _ A k _
  simp only [zero_left]
  exact hasDerivAt_const 0 0

private theorem zero_grain (p : BudgetPoint) (s : Support n) (v : Site n) :
    Mix.grain p s (fun _ : Config G n => (0 : ℂ)) v 0 := by
  refine ⟨fun _ => 0, fun _ => le_rfl, ?_, ?_⟩
  · simp only [zero_div, Finset.sum_const_zero, le_refl]
  intro k _ _ U _
  simp only [zero_left, norm_zero, le_refl]

/-- One original layout receipt precedes every later test. The nonempty
native marks survive even for identically zero rows. -/
theorem vacuumRemainder_active (T : Taste X o P R) (x₀ : X)
    (h : (T.leaf x₀).Active) (x : X) :
    ((vacuumRemainder T).leaf x).Active := by
  constructor
  · refine ⟨h.articles.proper, h.articles.pins, fun i => zero_regular _ _,
      h.articles.occurs, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hn
      exact False.elim (hn rfl)
    · intro i j U W hUW hFlags
      rfl
    · intro i j U hn
      exact False.elim (hn rfl)
    · intro i j
      exact measurable_const
    · intro i j g U
      rfl
  exact ⟨h.captions.card, h.captions.pins⟩

private theorem zero_budget {ι : Type*} : SumBudget (fun _ : ι => (0 : ℝ)) 0 :=
  ⟨fun _ => le_rfl, summable_zero, by simp⟩

/-- The common zero majorants work after an arbitrary fixed test pullback.
The original vacuum K is not part of this zero marked price. -/
def vacuumRemainder_fullBudget (T : Taste X o P R) (x₀ : X)
    (h : (T.leaf x₀).Active) (f : Y → X) (p : BudgetPoint)
    (w : V → ℝ) (κ : ℝ) (hw : ∀ v, 0 < w v) (hκ : 0 < κ) :
    FullBudget p (pullback f (vacuumRemainder T)) w κ 0 0 where
  white := fun _ => 0
  black := fun _ => 0
  gold := fun _ => 0
  unitBound := fun _ => 0
  active y := vacuumRemainder_active T x₀ h (f y)
  radii := hw
  divisor := hκ
  white_nonnegative _ := le_rfl
  regular _ := ⟨fun _ _ _ => zero_grain _ _ _⟩
  regular_law _ _ := zero_regular _ _
  black_nonnegative _ := le_rfl
  forced _ _ _ _ := by simp [pullback, vacuumRemainder]
  gold_nonnegative _ := le_rfl
  caption _ _ := by simp [pullback, vacuumRemainder]
  unit_nonnegative _ := le_rfl
  unit _ _ := by simp [pullback, vacuumRemainder]
  regularTotal v := by
    refine ⟨0, 0, ?_, ?_, by simp⟩
    · simpa [pullback, vacuumRemainder, BudgetPoint.mass] using
        (zero_budget (ι := ℕ))
    · simpa [pullback, vacuumRemainder, BudgetPoint.mass] using
        (zero_budget (ι := ℕ))
  forcedTotal v := by
    simpa [pullback, vacuumRemainder, BudgetPoint.mass] using
      (zero_budget (ι := ℕ × ℕ))

/-- Relative normalization changes none of the zero marked coefficients. -/
theorem vacuumRemainder_normalized_pullback (T : Taste X o P R)
    (f : Y → X) (cost : R.Mode → ℝ) :
    priceNormalized cost (pullback f (vacuumRemainder T)) =
      pullback f (vacuumRemainder T) := by
  simp only [priceNormalized, pullback, vacuumRemainder, smul_zero]

/-- All declared envelope products and positive radii are retained. -/
def vacuumRemainder_relativeBudget (T : Taste X o P R) (x₀ : X)
    (h : (T.leaf x₀).Active) (f : Y → X) (p : BudgetPoint)
    (w : V → ℝ) (κ : ℝ) (cost : R.Mode → ℝ)
    (hw : ∀ v, 0 < w v) (hκ : 0 < κ)
    (hc : ∀ s, 0 < cost s) (hq : cost R.quiet = 1) :
    RelativeBudget p (pullback f (vacuumRemainder T)) w κ cost 0 0 where
  positive := hc
  quiet := hq
  budget := by
    rw [vacuumRemainder_normalized_pullback]
    exact vacuumRemainder_fullBudget T x₀ h f p w κ hw hκ

variable [Fintype V]

/-- The auxiliary marked logarithm vanishes on the entire test/field space. -/
theorem vacuumRemainder_log (T : Taste X o P R) (x : X) (U : Config G n) :
    ((vacuumRemainder T).leaf x).log U = 0 := by
  simp [Taste.leaf, vacuumRemainder, View.terms, Deck.log, Bands.extra,
    Bands.ray, Captions.chord, masked]

omit [Fintype V] in
/-- Every packet is the original vacuum packet on its original labels. -/
theorem vacuumRemainder_packet (T : Taste X o P R) (x : X)
    (s : Finset ℕ) (U : Config G n) :
    ((vacuumRemainder T).leaf x).contents.packet s U =
      Poly.bead R (P.activities.gasOccurrence P.p s U : ℂ) := by
  change (if P.activities.admissible P.p U s then
    ∏ i ∈ s, (Poly.send R.quiet (P.activities.K i U : ℂ) +
      ∑' j, Poly.send (T.menu.marks i j) 0) else 0) = _
  simp only [Poly.send_zero, tsum_zero, add_zero]
  by_cases hs : P.activities.admissible P.p U s
  · rw [if_pos hs]
    rw [Activities.gasOccurrence, if_pos hs]
    change (∏ i ∈ s, Poly.bead R (P.activities.K i U : ℂ)) =
      Poly.bead R ((∏ i ∈ s, P.activities.K i U : ℝ) : ℂ)
    rw [Complex.ofReal_prod, map_prod]
  · simp [Activities.gasOccurrence, hs]

/-- Absolute summability belongs to the unchanged original vacuum gas.
No affine-null condition or zero-vacuum-K assumption is introduced. -/
theorem vacuumRemainder_density (T : Taste X o P R) (x : X)
    (U : Config G n)
    (hGas : Summable (fun s : Finset ℕ =>
      ‖P.activities.gasOccurrence P.p s U‖)) :
    ((vacuumRemainder T).leaf x).density U =
      (P.eval U : ℂ) • (1 : Poly R) := by
  have hSend : Summable (fun s : Finset ℕ =>
      Poly.bead R (P.activities.gasOccurrence P.p s U : ℂ)) := by
    apply (Poly.budgeted (fun _ => zero_lt_one) hGas ?_).1
    intro s
    change Poly.price (fun _ : V => (1 : ℝ))
      (Poly.send R.quiet (P.activities.gasOccurrence P.p s U : ℂ)) ≤ _
    rw [Poly.solo, Poly.quiet_toll, one_mul, Complex.norm_real]
  have hCluster : ((vacuumRemainder T).leaf x).contents.cluster U =
      Poly.bead R (P.activities.gas P.p U : ℂ) := by
    change (∑' s, ((vacuumRemainder T).leaf x).contents.packet s U) = _
    simp_rw [vacuumRemainder_packet]
    ext j
    rw [Poly.share hSend]
    change (∑' s, (Poly.send R.quiet
      (P.activities.gasOccurrence P.p s U : ℂ)).part j) =
      (Poly.send R.quiet (P.activities.gas P.p U : ℂ)).part j
    simp only [Poly.part_send]
    by_cases hj : j = R.quiet
    · subst j
      simp only [ite_true, Activities.gas, Complex.ofReal_tsum]
    simp only [if_neg hj, tsum_zero]
  have hPass : Poly.pass (0 : Poly R) = 1 := by
    unfold Poly.pass
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi
      simp [zero_pow hi]
    · simp
  have hBead : Poly.bead R (P.activities.gas P.p U : ℂ) =
      (P.activities.gas P.p U : ℂ) • (1 : Poly R) := by
    simpa only [mul_one] using
      (Poly.product_bead (1 : Poly R) (P.activities.gas P.p U : ℂ))
  change (Real.exp (P.exponent U) : ℂ) •
    (Poly.pass (((vacuumRemainder T).leaf x).log U) *
      ((vacuumRemainder T).leaf x).contents.cluster U) = _
  rw [vacuumRemainder_log, hPass, one_mul, hCluster, hBead, smul_smul]
  congr 1
  exact (Complex.ofReal_mul _ _).symm

end YM.Integration.LocalComparison
