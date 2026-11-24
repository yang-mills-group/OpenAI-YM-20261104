import YM.Integration.LocalComparisonEnvelope
import YM.Overlay.Pays
import YM.Ac.Tree
import YM.Push.ABSOLUTE_SUMS.Basic

/-!
A concrete weak incoming reserve for the original vacuum rows and the actual
marked rows of a common representation. The marked charge is its predivision
mass, card V * (κ * E), and the vacuum fugacity is w0^(-θ). One unit of support
exponent is spent in Ac.forest. Neither an output reserve nor a Gaussian or
original-partition comparison is assumed or concluded here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker
open RG3.Held RG3.Forms RG3.Script.Picnic Push.AbsoluteSums
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V]
    {R : Census V} {X : Type*} {P : Rep G n} {o : V → Site n}
    {p : BudgetPoint} {T : Taste X o P R} {w : V → ℝ}
    {κ regularPrice E : ℝ}

/-- The exact marked coefficient mass, retaining every address and mode. -/
def FullBudget.weakMarkedMass (h : FullBudget p T w κ regularPrice E)
    (ij : ℕ × ℕ) : ℝ :=
  Poly.toll w (T.menu.marks ij.1 ij.2) *
    p.mass (P.activities.forced ij.1).support (h.black ij)

lemma FullBudget.weakMarkedMass_nonneg (h : FullBudget p T w κ regularPrice E)
    (ij : ℕ × ℕ) : 0 ≤ h.weakMarkedMass ij :=
  mul_nonneg (Poly.worth h.radii _).le
    ((h.black_nonnegative ij).trans (p.loMass _ _ (h.black_nonnegative ij)))

/-- Remove precisely the reserved support weight from the total at one original
forced address. This majorant is chosen before every independent test. -/
def FullBudget.weakMarkedWeight (h : FullBudget p T w κ regularPrice E)
    (i : ℕ) : ℝ :=
  Real.exp (-p.supportExponent * coverNumber p.B (P.activities.forced i).support) *
    ∑' j, h.weakMarkedMass (i, j)

lemma FullBudget.weakMarkedWeight_nonneg (h : FullBudget p T w κ regularPrice E)
    (i : ℕ) : 0 ≤ h.weakMarkedWeight i :=
  mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun j => h.weakMarkedMass_nonneg (i, j))

variable [Fintype V]

/-- An inhabitant exposes the fixed nonempty marked modes; the mass itself does
not depend on this inhabitant. There is no lattice-volume factor. -/
lemma FullBudget.weakMarked_total (h : FullBudget p T w κ regularPrice E) (x : X) :
    SumBudget h.weakMarkedMass ((Fintype.card V : ℝ) * (κ * E)) :=
  Overlay.per_system h.weakMarkedMass_nonneg
    (fun ij => (h.active x).articles.occurs ij.1 ij.2) h.forcedTotal

/-- Uniform control of the actual marked part of each original forced row. -/
lemma FullBudget.weakMarked_bound (h : FullBudget p T w κ regularPrice E)
    (x : X) (U : Config G n) (i : ℕ) :
    Poly.price w ((T.leaf x).contents.each i U -
      Poly.bead R (P.activities.K i U : ℂ)) ≤ h.weakMarkedWeight i := by
  obtain ⟨hFiber, _⟩ := (summable_prod_of_nonneg
    (show 0 ≤ h.weakMarkedMass from h.weakMarkedMass_nonneg)).mp
      (h.weakMarked_total x).2.1
  have hCancel :
      Real.exp (-p.supportExponent * coverNumber p.B (P.activities.forced i).support) *
      Real.exp (p.supportExponent * coverNumber p.B (P.activities.forced i).support) = 1 := by
    rw [← Real.exp_add, show
      -p.supportExponent * coverNumber p.B (P.activities.forced i).support +
       p.supportExponent * coverNumber p.B (P.activities.forced i).support = 0 by ring,
      Real.exp_zero]
  have hTagged (j : ℕ) : Poly.price w ((T.leaf x).contents.tagged i j U) ≤
      Real.exp (-p.supportExponent * coverNumber p.B (P.activities.forced i).support) *
        h.weakMarkedMass (i, j) := by
    change Poly.price w (Poly.send (T.menu.marks i j) (T.menu.force x i j U)) ≤ _
    rw [Poly.solo]
    calc
      _ ≤ Poly.toll w (T.menu.marks i j) * h.black (i, j) :=
        mul_le_mul_of_nonneg_left (h.forced x i j U) (Poly.worth h.radii _).le
      _ = (Real.exp (-p.supportExponent * coverNumber p.B (P.activities.forced i).support) *
          Real.exp (p.supportExponent * coverNumber p.B (P.activities.forced i).support)) *
            (Poly.toll w (T.menu.marks i j) * h.black (i, j)) := by rw [hCancel, one_mul]
      _ = _ := by unfold FullBudget.weakMarkedMass BudgetPoint.mass; ring
  change Poly.price w ((Poly.bead R (P.activities.K i U : ℂ) +
    ∑' j, (T.leaf x).contents.tagged i j U) -
      Poly.bead R (P.activities.K i U : ℂ)) ≤ h.weakMarkedWeight i
  rw [add_sub_cancel_left]
  obtain ⟨_, hPrice⟩ := Poly.budgeted h.radii
    ((hFiber i).mul_left (Real.exp
      (-p.supportExponent * coverNumber p.B (P.activities.forced i).support))) hTagged
  exact hPrice.trans_eq (by unfold FullBudget.weakMarkedWeight; rw [tsum_mul_left])

/-- A weak incoming condition with an explicit support reserve. The regular
price is unrestricted because this criterion consumes only forced rows. -/
structure WeakReserve (p : BudgetPoint) (T : Taste X o P R) (w : V → ℝ)
    (κ regularPrice E a w0 θ : ℝ) where
  vacuum : P.activities.KBound p w0
  marked : FullBudget p T w κ regularPrice E
  vacuum_positive : 0 < w0
  vacuum_small : w0 ≤ 1
  fugacity_nonnegative : 0 ≤ θ
  fugacity_lt_one : θ < 1
  output_nonnegative : 0 ≤ a
  support_reserve : a + 1 ≤ p.supportExponent
  tree_reserve : (p.B + p.B + 1 : ℕ)^4 *
    (w0^(1-θ) + (Fintype.card V : ℝ) * (κ * E)) ≤ 1

variable {a w0 θ : ℝ}

/-- The original vacuum row receives only its declared fugacity; the marked
weight is the exact common majorant already carried by FullBudget. -/
def WeakReserve.weight (h : WeakReserve p T w κ regularPrice E a w0 θ)
    (k : ℕ → ℝ) (i : ℕ) : ℝ :=
  w0^(-θ) * k i + h.marked.weakMarkedWeight i

/-- The concrete intake supplies the native hit and tree receipts, together
with a test-uniform majorant for the original full row. The unused support
exponent beyond a+1 remains visible in support_reserve. -/
theorem WeakReserve.native_forest (h : WeakReserve p T w κ regularPrice E a w0 θ)
    (x0 : X) :
    ∃ k : ℕ → ℝ,
      (∀ i, 0 ≤ k i ∧ ∀ U, ‖P.activities.K i U‖ ≤ k i) ∧
      (∀ y : Site n, SumBudget (fun i => if y ∈ (P.activities.forced i).support
        then p.mass (P.activities.forced i).support (k i) else 0) w0) ∧
      (∀ i, 0 ≤ h.weight k i) ∧
      (∀ (x : X) (U : Config G n) i,
        Poly.price w ((T.leaf x).contents.each i U) ≤ h.weight k i) ∧
      Ac.Hit (fun i => (P.activities.forced i).support) p.B (h.weight k) (a+1)
        (w0^(1-θ) + (Fintype.card V : ℝ) * (κ * E)) ∧
      (∀ y : Site n, SumBudget
        (Ac.roots (fun i => (P.activities.forced i).support) p.B (h.weight k) a y)
        (Real.exp (w0^(1-θ) + (Fintype.card V : ℝ) * (κ * E)) - 1)) := by
  obtain ⟨k, hk, hK⟩ := h.vacuum
  let fugacity := w0^(-θ)
  let M := (Fintype.card V : ℝ) * (κ * E)
  let γ := w0^(1-θ) + M
  have hfugacity : 1 ≤ fugacity := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    h.vacuum_positive h.vacuum_small (neg_nonpos.mpr h.fugacity_nonnegative)
  have hfugacity0 : 0 ≤ fugacity := zero_le_one.trans hfugacity
  have hfugacityw : fugacity * w0 = w0^(1-θ) := by
    calc
      _ = w0^(-θ) * w0^(1 : ℝ) := by rw [Real.rpow_one]
      _ = w0^(-θ+1) := (Real.rpow_add h.vacuum_positive _ _).symm
      _ = _ := by congr 1; ring
  have hf (i) : 0 ≤ h.weight k i :=
    add_nonneg (mul_nonneg hfugacity0 (hk i).1) (h.marked.weakMarkedWeight_nonneg i)
  have hEach (x : X) (U : Config G n) (i : ℕ) :
      Poly.price w ((T.leaf x).contents.each i U) ≤ h.weight k i := by
    have hScalar : Poly.price w (Poly.bead R (P.activities.K i U : ℂ)) ≤ fugacity * k i := by
      change Poly.price w (Poly.send R.quiet (P.activities.K i U : ℂ)) ≤ _
      rw [Poly.solo, Poly.quiet_toll, one_mul, Complex.norm_real]
      exact ((hk i).2 U).trans (by simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hfugacity (hk i).1))
    have he := Poly.addition h.marked.radii
      ((T.leaf x).contents.each i U - Poly.bead R (P.activities.K i U : ℂ))
      (Poly.bead R (P.activities.K i U : ℂ))
    rw [sub_add_cancel] at he
    exact (he.trans (add_le_add (h.marked.weakMarked_bound x U i) hScalar)).trans_eq
      (add_comm _ _)
  have hTotal := h.marked.weakMarked_total x0
  obtain ⟨_, hOuter⟩ := (summable_prod_of_nonneg
    (show 0 ≤ h.marked.weakMarkedMass from h.marked.weakMarkedMass_nonneg)).mp hTotal.2.1
  have hRestore (i) : h.marked.weakMarkedWeight i * Real.exp
      (p.supportExponent * coverNumber p.B (P.activities.forced i).support) =
      ∑' j, h.marked.weakMarkedMass (i, j) := by
    unfold FullBudget.weakMarkedWeight
    calc
      _ = (Real.exp (-p.supportExponent * coverNumber p.B (P.activities.forced i).support) *
          Real.exp (p.supportExponent * coverNumber p.B (P.activities.forced i).support)) *
          ∑' j, h.marked.weakMarkedMass (i, j) := by ring
      _ = _ := by
        rw [← Real.exp_add, show
          -p.supportExponent * coverNumber p.B (P.activities.forced i).support +
           p.supportExponent * coverNumber p.B (P.activities.forced i).support = 0 by ring,
          Real.exp_zero, one_mul]
  have hMarked (I : Finset ℕ) : (∑ i ∈ I, h.marked.weakMarkedWeight i * Real.exp
      (p.supportExponent * coverNumber p.B (P.activities.forced i).support)) ≤ M := by
    simp_rw [hRestore]
    exact (hOuter.sum_le_tsum I (fun i _ => tsum_nonneg fun j =>
      h.marked.weakMarkedMass_nonneg (i, j))).trans
        ((hTotal.2.1.tsum_prod).symm.trans_le hTotal.2.2)
  have hBase (y : Site n) (I : Finset ℕ) :
      (∑ i ∈ I, if y ∈ (P.activities.forced i).support then
        k i * Real.exp (p.supportExponent * coverNumber p.B (P.activities.forced i).support)
        else 0) ≤ w0 := by
    simpa only [BudgetPoint.mass, mul_comm] using budget_sum (hK y) I
  have hBig : Ac.Hit (fun i => (P.activities.forced i).support) p.B
      (h.weight k) p.supportExponent (fugacity * w0 + M) := by
    intro y
    refine budget_of_sum (fun i => by
      split_ifs
      · exact mul_nonneg (hf i) (Real.exp_pos _).le
      · exact le_rfl) fun I => ?_
    calc
      _ ≤ fugacity * (∑ i ∈ I, if y ∈ (P.activities.forced i).support then
          k i * Real.exp (p.supportExponent * coverNumber p.B (P.activities.forced i).support)
          else 0) + ∑ i ∈ I, h.marked.weakMarkedWeight i * Real.exp
            (p.supportExponent * coverNumber p.B (P.activities.forced i).support) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · exact (show h.weight k i * Real.exp _ =
            fugacity * (k i * Real.exp _) + h.marked.weakMarkedWeight i * Real.exp _ by
              unfold WeakReserve.weight; dsimp [fugacity]; ring).le
        · simp only [mul_zero, zero_add]
          exact mul_nonneg (h.marked.weakMarkedWeight_nonneg i) (Real.exp_pos _).le
      _ ≤ fugacity * w0 + M := add_le_add (mul_le_mul_of_nonneg_left (hBase y I) hfugacity0) (hMarked I)
  have hHit : Ac.Hit (fun i => (P.activities.forced i).support) p.B
      (h.weight k) (a+1) γ := by
    intro y
    have hy : SumBudget (fun i => if y ∈ (P.activities.forced i).support then
        h.weight k i * Real.exp (p.supportExponent *
          coverNumber p.B (P.activities.forced i).support) else 0) γ := by
      simpa only [hfugacityw] using hBig y
    refine budget_mono hy (fun i => by
      split_ifs
      · exact mul_nonneg (hf i) (Real.exp_pos _).le
      · exact le_rfl) fun i => ?_
    split_ifs
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right h.support_reserve (Nat.cast_nonneg _))) (hf i)
    · exact le_rfl
  have hγ : 0 ≤ γ := add_nonneg (Real.rpow_nonneg h.vacuum_positive.le _) (budget_nonneg hTotal)
  exact ⟨k, hk, hK, hf, hEach, hHit,
    Ac.forest _ _ h.output_nonnegative hf hHit h.tree_reserve hγ⟩

end YM.Integration.LocalComparison
