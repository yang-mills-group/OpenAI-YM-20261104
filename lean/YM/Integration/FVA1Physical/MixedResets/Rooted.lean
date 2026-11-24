import YM.QuadraticLocal.Neighborhood.Door
import YM.QuadraticLocal.Lamps

/-!
# Reader norm for the mixed part

Work in the native common `Gallery` representation. The Hit-budget version
is stronger than the mixed norm with a sum for each prescribed marker. To remove
all ambiguity about this point (especially re global marks, huge index sets and
location of the test and root suprema), give the joint multi-mark norm directly with the
regular marked rate. Regular factorial summability even for
post-choice hull roots and fields and independently selected directions. Forced
price here keeps the strong divisor and does not differentiate Borel kernels. Use
only on the packed Gallery of the exact difference, never on an evaluated density
divided by the conditional vacuum. Caps on the *sum* over all other mark positions.

Supports and masses are original (incl flags in the forced sum). No deletion of
large sets/winding clusters or restriction to unmasked link fields. `exp` exponent
may grow. No claim of factorial norm entitlement stronger than the Arena supports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.MixedResets
open Function Filter Finset Lattice RG Wilson Marker Ac
open QuadraticLocal
open Push.Corrected Push.AbsoluteSums MeasureTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {V ι X : Type} [Fintype V] [DecidableEq V]
    {I : Marker.Census V} {o : V → Site n} {P : Rep G n}
    (L : QuadraticLocal.Gallery X ι o P I) (w : V → ℝ) (κ : ℝ) (reserve : ℝ)

set_option quotPrecheck false

/-- `reserve` additional *regular* support exponent. Bills in this theorem
(as bought from CP5) have `reserve≥0`. Carry the forced support exponent literally
at `p.supportExponent` (can retain smaller declared reserves within it). -/
structure Rooted (regular force : ℝ) : Prop where
  divisor : 0 < κ
  positive i : 0 < w i
  white : ∃ f : ι → ℝ,
    (∀ i, 0 ≤ f i) ∧
    (∀ i t x, x ∈ L.E.ground i → Mix.grain P.p (L.E.ground i) (L.E.nominal t i) x (f i)) ∧
    ∀ v : V, SumBudget (fun i : ι => if v ∈ (L.E.mode i).val then Poly.toll w (L.E.mode i) * Mix.loaf P.p (L.E.ground i) reserve (f i) else 0) regular
  hard : ∃ g : ℕ → I.Mode → ℝ,
    (∀ k i, 0 ≤ g k i) ∧
    (∀ k i t U, ‖(L.K.hard t k U).part i‖ ≤ g k i) ∧
    (∀ k i, 0 < g k i → ∀ v ∈ i.val, o v ∈ (P.activities.forced k).support) ∧
    ∀ v : V, SumBudget (fun k => (∑ i : I.Mode, if v ∈ i.val then Poly.toll w i * P.p.mass (P.activities.forced k).support (g k i) else 0)/κ) force

variable {reg fee : ℝ}
include L
set_option maxHeartbeats 500000 in
lemma hit_rooted (hl : L.E.Paid w P.p.B (P.p.supportExponent + reserve) reg)
    (hk : L.K.Paid w P.p.B P.p.supportExponent (fee * κ))
    (divisor : 0 < κ) (hw : ∀ i, 0 < w i) : Rooted L w κ reserve (3 * reg) fee := by
  obtain ⟨f,nice,hf,hcap⟩ := hl.budget
  obtain ⟨g,cover,hK⟩ := hk.wages
  let pos (i : I.Mode) := (Poly.worth hw i).le
  constructor
  · exact divisor
  · exact hw
  · refine ⟨fun i => 3*f i, fun i => mul_nonneg (by norm_num) (nice _),
      fun i t x hx => Neighborhood.outBound x (L.E.nominal t i) (hf i t _ hx), fun v => ?_⟩
    apply budget_mono (budget_scale (by norm_num : 0 ≤ (3:ℝ)) (hcap (o v)))
    · intro i; split
      · exact mul_nonneg (pos _) (mul_nonneg (Real.exp_nonneg _) (mul_nonneg (by norm_num) (nice _)))
      · exact le_rfl
    intro i; split
    · next h =>
      change _ ≤ 3*(if o v ∈ L.E.ground i then _ else 0)
      rw [if_pos (show o v ∈ L.E.ground i from L.E.roots i v h)]
      unfold Mix.loaf; nlinarith only []
    · exact mul_nonneg (by norm_num : 0 ≤ (3:ℝ)) ((hcap _).1 _)
  let ok k (i : I.Mode) := ∀ v ∈ i.val, o v ∈ (P.activities.forced k).support
  let f k (i : I.Mode) := if ok k i then ‖(g k).part i‖ else 0
  have hf k i : 0 ≤ f k i := by unfold f; split; exact norm_nonneg _; exact le_rfl
  refine ⟨f, hf, fun k i t U => ?_, fun k i hh v hv => ?_, fun v => ?_⟩
  · unfold f
    split
    · next h => exact ((cover k t U i).1.trans_eq ((cover k t U).norm i).symm)
    · next h =>
      rw [not_not.mp (fun hh => h ((L.K.locality t k).carry U i hh)), norm_zero]
  · unfold f at hh; split at hh
    · next H => exact H v hv
    linarith only [hh]
  have bound := budget_scale (inv_pos.mpr divisor).le (hK (o v))
  rw [mul_comm κ⁻¹, mul_assoc, mul_inv_cancel₀ divisor.ne', mul_one] at bound
  let a (k : ℕ) := Real.exp ((P.p).supportExponent * coverNumber (P.p).B ((P.activities.forced k).support))
  have hl1 k (i : I.Mode) : 0 ≤ (if v∈i.val then Poly.toll w i * P.p.mass (P.activities.forced k).support (f k i) else 0) := by
    split; exact mul_nonneg (pos _) (mul_nonneg (Real.exp_pos _).le (hf ..)); exact le_rfl
  refine budget_mono bound (fun k => div_nonneg (sum_nonneg (fun i _ => hl1 k i)) divisor.le) ?_
  intro k; change _ ≤ κ⁻¹ * (if o v∈ (P.activities.forced k).support then _ else (0:ℝ)) -- rw mul_comm changed in lhs of bound?
  rw [div_eq_inv_mul]; apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr divisor).le
  split
  · change (∑ i:I.Mode, if v∈ i.val then Poly.toll w i * (a k * f k i) else 0) ≤ Poly.price w (g k) * a k
    unfold Poly.price; rw [sum_mul]; apply sum_le_sum
    intro i _; split
    · unfold f; split
      · nlinarith only []
      rw [mul_zero, mul_zero]; exact mul_nonneg (mul_nonneg (pos _) (norm_nonneg _)) (Real.exp_pos _).le
    exact mul_nonneg (mul_nonneg (pos _) (norm_nonneg _)) (Real.exp_pos _).le
  · next h =>
    apply le_of_eq (sum_eq_zero _)
    intro i _; split
    · next he =>
      unfold f BudgetPoint.mass; rw [if_neg (fun H => h (H v he)), mul_zero, mul_zero]
    · rfl
end YM.Integration.FVA1Physical.MixedResets
