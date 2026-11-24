import YM.Integration.WilsonFormalSupplier
import YM.XSpace.Tipping
import YM.XSpace.Flares

/-!
# The retained Wilson section at leading infrared order

The polynomial is the leading RG06 coefficient of the original local
section.  Its finite expectation uses the actual inversion-tree covariance.
The period comparison includes the image term and is uniform in the tree
and in every translated insertion point in the stated common bulk window.

These statements concern the leading Gaussian coefficient.  They do not
identify the full predictor-history measure with the bare inversion measure.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualLeadingIR

open Function Filter Lattice Wilson Source
open XSpace XSpace.Chart2 XSpace.JetGauge XSpace.Outline XSpace.Comets
open Next.Rank.Normal
open scoped BigOperators Classical Topology

variable {G : Gauge} (C : Family G)

/-- Every basis column is lowered by its own original slot count before
the independently chosen coefficients are combined. -/
def leading (d : ℕ) (v : C.label d) : St ℤ G :=
  ∑ i, v i • RG06.Tokens.stencil (C.localSection d) i 0

private theorem chart_input_gradient {Q : Type*} [AddCommGroup Q] [One Q]
    (c : Outline.Chart ℤ Q) (A : LogLinks Q G) (w : Four Q → G.Color) (t : ℝ) :
    c.input (A + t • grad w) = c.input A +
      RG06.Tokens.latticeGradient (fun z => (-t) • w (c.site z)) := by
  funext e
  change A (c.site e.1, e.2) + t • (w (c.site e.1 + step e.2) - w (c.site e.1)) =
    A (c.site e.1, e.2) +
      ((-t) • w (c.site e.1) - (-t) • w (c.site (e.1 + step e.2)))
  rw [c.next, smul_sub, neg_smul, neg_smul]
  abel

/-- Horizontality follows from the original section's proved valuation;
it is not a new condition on the infrared input. -/
theorem basis_horizontal {Q : Type*} [AddCommGroup Q] [One Q]
    (d : ℕ) (hV : Bid.pop (C.localSection d))
    (i : (C.labels.level d).Index) (c : Outline.Chart ℤ Q)
    (w : Four Q → G.Color) :
    D (grad w) (c.pull (RG06.Tokens.stencil (C.localSection d) i 0)) = 0 := by
  apply Chart2.same
  intro A
  rw [map_zero]
  have h (t : ℝ) :
      pit (A + t • grad w) (c.pull (RG06.Tokens.stencil (C.localSection d) i 0)) =
        pit A (c.pull (RG06.Tokens.stencil (C.localSection d) i 0)) := by
    rw [c.pull_point, c.pull_point, chart_input_gradient]
    exact RG06.Tokens.horizontal (C.localSection d) hV i (c.input A)
      (fun z => (-t) • w (c.site z))
  have hd := Chart2.directional A (grad w)
    (c.pull (RG06.Tokens.stencil (C.localSection d) i 0))
  simp_rw [h] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) _)

theorem leading_horizontal {Q : Type*} [AddCommGroup Q] [One Q]
    (d : ℕ) (hV : Bid.pop (C.localSection d)) (v : C.label d)
    (c : Outline.Chart ℤ Q) (w : Four Q → G.Color) :
    D (grad w) (c.pull (leading C d v)) = 0 := by
  simp only [leading, map_sum, map_smul]
  simp only [(D (grad w)).map_smul, basis_horizontal C d hV, smul_zero,
    Finset.sum_const_zero]

variable {I : Type*} [Fintype I] (d : I → ℕ)

/-- All original marked columns occur in one polynomial before Wick
evaluation, so mixed contractions and the empty product are retained. -/
def marked (v : (i : I) → C.label (d i)) : Outline.Shadow (G := G) (Z := I) :=
  ∏ i, MvPolynomial.rename (Prod.mk i) (leading C (d i) (v i))

theorem marked_motor {Q : Type*} [AddCommGroup Q] [One Q]
    (v : (i : I) → C.label (d i)) (g : Outline.Given G Q) (x : I → Four Q) :
    Outline.motor g x (marked C d v) =
      ∏ i, (g.points (x i)).pull (leading C (d i) (v i)) := by
  simp only [marked, map_prod, Outline.motor_at]

omit [Fintype I] in
private theorem product_horizontal {Q : Type*} [AddCommGroup Q] [One Q]
    (w : Four Q → G.Color) (p : I → St Q G)
    (h : ∀ i, D (grad w) (p i) = 0) (s : Finset I) :
    D (grad w) (∏ i ∈ s, p i) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, (D (grad w)).leibniz, h, ih]
    simp

theorem marked_horizontal (hV : ∀ i, Bid.pop (C.localSection (d i)))
    (v : (i : I) → C.label (d i)) (R : XSpace.Period) (x : I → R.Sites)
    (w : R.Sites → G.Color) :
    D (grad w) (Outline.motor (Outline.dawn G R) x (marked C d v)) = 0 := by
  rw [marked_motor]
  exact product_horizontal w _
    (fun i => leading_horizontal C (d i) (hV i) (v i) _ w) Finset.univ

private theorem horizontal_tree (R : XSpace.Period) (T : R.Tree)
    (p : St (Per R.side) G) (h : ∀ w, D (grad w) p = 0) :
    E (treeCov T G) p = E (Outline.dawn G R).grant p := by
  let Y : PowerSeries (St (Per R.side) G) := PowerSeries.X * PowerSeries.C p
  have hz : PowerSeries.constantCoeff Y = 0 := by simp [Y]
  have hs : PowerSeries.coeff 1 Y = p := by
    unfold Y
    rw [PowerSeries.coeff_one_mul]
    simp
  have hp : price1 (R := R) Y = p := by
    simp only [price1, hs, hz, mul_zero, sub_zero]
  have hY : Good (R := R) Y := by
    constructor <;> intros <;> simp only [hz, hs, map_zero, h, neg_zero]
  rw [← hp, ← setting T (Feynman.meet G R) hY, hp]
  rfl

/-- The finite coefficient uses the original inverse Hessian on this
tree, not an independently postulated covariance. -/
def finite (v : (i : I) → C.label (d i)) (R : XSpace.Period) (T : R.Tree)
    (x : I → Cover) : ℂ :=
  E (treeCov T G) (Outline.motor (Outline.dawn G R)
    (wrap R.side ∘ x) (marked C d v))

def cover (v : (i : I) → C.label (d i)) (x : I → Cover) : ℂ :=
  E (Outline.dusk G).grant (Outline.motor (Outline.dusk G) x (marked C d v))

/-- This is the coefficient of the native normalized Gaussian polynomial
input, including its unit vacuum, on the same inversion tree. -/
theorem finite_normalized (v : (i : I) → C.label (d i))
    (R : XSpace.Period) (T : R.Tree) (x : I → Cover) :
    finite C d v R T x = PowerSeries.constantCoeff
      (Bare.normalized T G (PowerSeries.C
        (tea T (Outline.motor (Outline.dawn G R) (wrap R.side ∘ x) (marked C d v))))) := by
  rw [Bare.leading, PowerSeries.constantCoeff_C, Chart2.transfers]
  rfl

theorem finite_dawn (hV : ∀ i, Bid.pop (C.localSection (d i)))
    (v : (i : I) → C.label (d i)) (R : XSpace.Period) (T : R.Tree)
    (x : I → Cover) :
    finite C d v R T x =
      E (Outline.dawn G R).grant
        (Outline.motor (Outline.dawn G R) (wrap R.side ∘ x) (marked C d v)) :=
  horizontal_tree R T _ (marked_horizontal C d hV v R _)

/-- Quantitative removal of the period and inversion image for every
original leading-column mixture. The independent-coefficient uniform
version below will choose its constant before those mixtures. -/
theorem comparison (hV : ∀ i, Bid.pop (C.localSection (d i)))
    (v : (i : I) → C.label (d i)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (R : XSpace.Period) (T : R.Tree) (o : Cover),
      Comets.Tall R o → ∀ (r : ℕ) (x : I → Cover),
      (∀ i, Sail.reach (x i - o) ≤ r) →
      ‖finite C d v R T x - cover C d v x‖ ≤ A * Comets.budget R r := by
  obtain ⟨A, hA, H⟩ := (Comets.arc (marked C d v)).1
  refine ⟨A, hA, ?_⟩
  intro R T o ho r x hx
  rw [finite_dawn C d hV]
  exact H R o ho r x hx

theorem leading_single (j : ℕ) (i : (C.labels.level j).Index) :
    leading C j (Pi.single i 1) = RG06.Tokens.stencil (C.localSection j) i 0 := by
  simp [leading, Pi.single_apply]

/-- One independent original basis choice at each marked root. -/
abbrev Choices := (i : I) → (C.labels.level (d i)).Index

def basisInput (b : Choices C d) (i : I) : C.label (d i) := Pi.single (b i) 1

theorem marked_expansion (v : (i : I) → C.label (d i)) :
    marked C d v = ∑ b : Choices C d, (∏ i, v i (b i)) • marked C d (basisInput C d b) := by
  simp only [marked, leading, map_sum, map_smul]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.prod_smul]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp [basisInput, Pi.single_apply]

theorem finite_expansion (v : (i : I) → C.label (d i))
    (R : XSpace.Period) (T : R.Tree) (x : I → Cover) :
    finite C d v R T x = ∑ b : Choices C d,
      (∏ i, v i (b i)) * finite C d (basisInput C d b) R T x := by
  unfold finite
  rw [marked_expansion]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem cover_expansion (v : (i : I) → C.label (d i)) (x : I → Cover) :
    cover C d v x = ∑ b : Choices C d,
      (∏ i, v i (b i)) * cover C d (basisInput C d b) x := by
  unfold cover
  rw [marked_expansion]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- The original coefficient mass in each independently chosen marked
column, multiplied only after each column's mass has been computed. -/
def inputMass (v : (i : I) → C.label (d i)) : ℝ :=
  ∏ i, ∑ j, ‖v i j‖

theorem inputMass_nonneg (v : (i : I) → C.label (d i)) : 0 ≤ inputMass C d v :=
  Finset.prod_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem inputMass_smul (a : I → ℂ) (v : (i : I) → C.label (d i)) :
    inputMass C d (fun i => a i • v i) = (∏ i, ‖a i‖) * inputMass C d v := by
  simp only [inputMass, Pi.smul_apply, norm_smul, ← Finset.mul_sum,
    Finset.prod_mul_distrib]

/-- Exact physical engineering factors, with no adjustment of the
independently chosen source coefficients or original horizons. -/
def engineeredInput (N : ℕ) (v : (i : I) → C.label (d i)) :
    (i : I) → C.label (d i) := fun i => Dict06.Actual.factor C N (d i) • v i

def engineeringScale (N : ℕ) : ℝ := ∏ i, (C.S.a N) ^ d i

theorem engineeringScale_pos (N : ℕ) : 0 < engineeringScale C d N :=
  Finset.prod_pos fun _ _ => pow_pos (C.S.a_pos N) _

theorem engineeredInput_mass (N : ℕ) (v : (i : I) → C.label (d i)) :
    engineeringScale C d N * inputMass C d (engineeredInput C d N v) = inputMass C d v := by
  change engineeringScale C d N *
    inputMass C d (fun i => Dict06.Actual.factor C N (d i) • v i) = inputMass C d v
  rw [inputMass_smul, ← mul_assoc]
  have hf (i : I) : ‖Dict06.Actual.factor C N (d i)‖ = ((C.S.a N) ^ d i)⁻¹ := by
    simp only [Dict06.Actual.factor, norm_inv, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (C.S.a_pos N)]
  simp_rw [hf]
  unfold engineeringScale
  rw [← Finset.prod_mul_distrib]
  simp only [mul_inv_cancel₀ (pow_ne_zero _ (C.S.a_pos N).ne'), Finset.prod_const_one, one_mul]

/-- One constant is fixed before every independently chosen column,
tree, period, bulk center and allowed marked configuration. The source
norms remain outside the infrared loss, with no volume factor. -/
theorem comparison_uniform (hV : ∀ i, Bid.pop (C.localSection (d i))) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (v : (i : I) → C.label (d i))
      (R : XSpace.Period) (T : R.Tree) (o : Cover),
      Comets.Tall R o → ∀ (r : ℕ) (x : I → Cover),
      (∀ i, Sail.reach (x i - o) ≤ r) →
      ‖finite C d v R T x - cover C d v x‖ ≤
        A * Comets.budget R r * inputMass C d v := by
  choose A hA H using fun b : Choices C d => comparison C d hV (basisInput C d b)
  let B : ℝ := ∑ b, A b
  have hB : 0 ≤ B := Finset.sum_nonneg fun b _ => hA b
  have hAB (b : Choices C d) : A b ≤ B :=
    Finset.single_le_sum (fun c _ => hA c) (Finset.mem_univ b)
  refine ⟨B, hB, ?_⟩
  intro v R T o ho r x hx
  rw [finite_expansion, cover_expansion, ← Finset.sum_sub_distrib]
  have bound (b : Choices C d) :
      ‖(∏ i, v i (b i)) * finite C d (basisInput C d b) R T x -
        (∏ i, v i (b i)) * cover C d (basisInput C d b) x‖ ≤
      (∏ i, ‖v i (b i)‖) * (B * Comets.budget R r) := by
    rw [← mul_sub, norm_mul, norm_prod]
    apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    exact (H b R T o ho r x hx).trans
      (mul_le_mul_of_nonneg_right (hAB b) (Comets.budget_pos R r).le)
  apply (norm_sum_le ..).trans
  apply (Finset.sum_le_sum fun b _ => bound b).trans_eq
  rw [← Finset.sum_mul]
  have hsum : (∑ b : Choices C d, ∏ i, ‖v i (b i)‖) = inputMass C d v :=
    (Fintype.prod_sum (fun i j => ‖v i j‖)).symm
  rw [hsum]
  ring

/-- The identical estimate for the actual engineering-scaled source,
with all ultraviolet factors removed explicitly on the left. -/
theorem comparison_engineered (hV : ∀ i, Bid.pop (C.localSection (d i))) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (N : ℕ) (v : (i : I) → C.label (d i))
      (R : XSpace.Period) (T : R.Tree) (o : Cover),
      Comets.Tall R o → ∀ (r : ℕ) (x : I → Cover),
      (∀ i, Sail.reach (x i - o) ≤ r) →
      engineeringScale C d N *
        ‖finite C d (engineeredInput C d N v) R T x - cover C d (engineeredInput C d N v) x‖ ≤
        A * Comets.budget R r * inputMass C d v := by
  obtain ⟨A, hA, H⟩ := comparison_uniform C d hV
  refine ⟨A, hA, ?_⟩
  intro N v R T o ho r x hx
  calc
    _ ≤ engineeringScale C d N *
        (A * Comets.budget R r * inputMass C d (engineeredInput C d N v)) :=
      mul_le_mul_of_nonneg_left (H _ R T o ho r x hx) (engineeringScale_pos C d N).le
    _ = A * Comets.budget R r *
        (engineeringScale C d N * inputMass C d (engineeredInput C d N v)) := by ring
    _ = _ := by rw [engineeredInput_mass]

/-- The leading polynomial is extracted from the actual calibrated
cutoff source, at its own shifted coefficient order. -/
theorem actual_cover_coefficient (N p j : ℕ) (i : (C.labels.level j).Index) :
    PowerSeries.coeff ((C.labels.level j).grades i).2
      (physicalCoverFilm C N p j
        (Dict06.Actual.calibrate C N p j ((C.labels.level j).basis i))) =
      Dict06.Actual.factor C N j • leading C j (Pi.single i 1) := by
  rw [leading_single]
  simpa only [RG06.Tokens.charge, Nat.zero_add, MvPolynomial.smul_eq_C_mul] using
    physicalCoverFilm_basis_coeff C j N p i 0

/-- The finite regulator is built on exactly the original schedule's
side. Both required geometric facts are already supplied by that schedule. -/
def actualPeriod (N p : ℕ) : XSpace.Period where
  side := C.side N p
  even := by
    obtain ⟨q, hq⟩ := C.S.side_four N p
    change (C.side N p).val = 4 * q at hq
    exact ⟨2 * q, by omega⟩
  large := by
    obtain ⟨q, hq⟩ := C.S.side_four N p
    change (C.side N p).val = 4 * q at hq
    have hp := (C.side N p).pos
    omega

/-- The independent period index in the retained schedule is cofinal
at every fixed ultraviolet cutoff. -/
theorem actual_side_tendsto (N : ℕ) :
    Tendsto (fun p => ((C.side N p).val : ℝ)) atTop atTop := by
  have h := (tendsto_natCast_atTop_atTop.comp C.S.period_strict.tendsto_atTop).atTop_mul_const
    (show (0 : ℝ) < (C.S.denominator N).val by exact_mod_cast (C.S.denominator N).pos)
  simpa only [Function.comp_apply, Family.side, Schedule.side, PNat.mul_coe, Nat.cast_mul] using h

theorem actual_budget_tendsto (N r : ℕ) :
    Tendsto (fun p => Comets.budget (actualPeriod C N p) r) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp (actual_side_tendsto C N)).const_mul (1 + (r : ℝ))
  simpa only [Function.comp_apply, Comets.budget, actualPeriod, div_eq_mul_inv, mul_zero] using h

/-- At fixed ultraviolet cutoff, every admitted family of the original
periods has zero leading infrared error. The center, placements and tree
may vary, while the source coefficients are fixed independently. -/
theorem actual_period_error_tendsto (hV : ∀ i, Bid.pop (C.localSection (d i)))
    (N r : ℕ) (v : (i : I) → C.label (d i))
    (T : (p : ℕ) → (actualPeriod C N p).Tree)
    (o : ℕ → Cover) (x : ℕ → I → Cover)
    (hbulk : ∀ᶠ p in atTop, Comets.Tall (actualPeriod C N p) (o p) ∧
      ∀ i, Sail.reach (x p i - o p) ≤ r) :
    Tendsto (fun p => finite C d v (actualPeriod C N p) (T p) (x p) - cover C d v (x p))
      atTop (𝓝 0) := by
  obtain ⟨A, _, H⟩ := comparison_uniform C d hV
  apply squeeze_zero_norm' (hbulk.mono fun p hp => H v _ (T p) (o p) hp.1 r (x p) hp.2)
  simpa only [mul_zero, zero_mul] using
    ((actual_budget_tendsto C N r).const_mul A).mul_const (inputMass C d v)

/-- Uniformity allows every independent test coefficient to vary with
the period. Only its explicit finite-dimensional input mass is bounded;
the discrepancy is estimated by the native period theorem. -/
theorem actual_uniform_error_tendsto (hV : ∀ i, Bid.pop (C.localSection (d i)))
    (N r : ℕ) (v : (p : ℕ) → (i : I) → C.label (d i)) (M : ℝ)
    (hmass : ∀ᶠ p in atTop, inputMass C d (v p) ≤ M)
    (T : (p : ℕ) → (actualPeriod C N p).Tree)
    (o : ℕ → Cover) (x : ℕ → I → Cover)
    (hbulk : ∀ᶠ p in atTop, Comets.Tall (actualPeriod C N p) (o p) ∧
      ∀ i, Sail.reach (x p i - o p) ≤ r) :
    Tendsto (fun p => finite C d (v p) (actualPeriod C N p) (T p) (x p) - cover C d (v p) (x p))
      atTop (𝓝 0) := by
  obtain ⟨A, hA, H⟩ := comparison_uniform C d hV
  have hb : ∀ᶠ p in atTop,
      ‖finite C d (v p) (actualPeriod C N p) (T p) (x p) - cover C d (v p) (x p)‖ ≤
        A * Comets.budget (actualPeriod C N p) r * M := by
    filter_upwards [hmass, hbulk] with p hm hp
    exact (H (v p) _ (T p) (o p) hp.1 r (x p) hp.2).trans
      (mul_le_mul_of_nonneg_left hm (mul_nonneg hA (Comets.budget_pos _ _).le))
  apply squeeze_zero_norm' hb
  simpa only [mul_zero, zero_mul] using
    ((actual_budget_tendsto C N r).const_mul A).mul_const M

end YM.Integration.ActualLeadingIR
