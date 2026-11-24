import YM.Integration.ZeroAwareIntrinsicRenderInvoice

/-!
# Capped intrinsic invoices on the original zero-aware rows

Only the auxiliary moment radius is capped. The original width in every
row budget, the support-cover reserve and all list occurrences are retained.
The resulting rank-specific factor is polynomial in the reciprocal width;
no upper bound on that width is required. Original permits supply only the
structural Invoice fields, and credit-only repricing preserves the complete
original activities. No actual coupling-ratio or next-admission payment is
inferred.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ZeroAwareCappedRenderInvoice

open Function Finset Lattice Wilson RG
open IterationFour.Vacuum LocalComparison.Global Extra.Iteration
open ZeroAwareIntrinsicRenderInvoice
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side}

def radius (width : ℝ) : ℝ := min (3 * width / 4) 1
def moment (d : ℕ) (width : ℝ) : ℝ := momentPrice d (radius width)

private theorem radius_pos {width : ℝ} (hw : 0 < width) :
    0 < radius width := lt_min (by positivity) zero_lt_one

private theorem moment_pos (d : ℕ) {width : ℝ} (hw : 0 < width) :
    0 < moment d width := momentPrice_pos d (radius_pos hw)

private theorem spend (d : ℕ) {width z : ℝ} (hw : 0 < width) (hz : 0 ≤ z) :
    (1 + z) ^ d ≤ moment d width * Real.exp ((3 * width / 4) * z) := by
  refine (spendMoment d (radius_pos hw) hz).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.exp_monotone (mul_le_mul_of_nonneg_right (min_le_left _ _) hz))
    (moment_pos d hw).le

/-- The cap removes exponential growth in the original width. -/
theorem moment_bound (d : ℕ) {width : ℝ} (hw : 0 < width) :
    moment d width ≤
      Real.exp 1 * d.factorial * (1 + (4 / 3 : ℝ) * width⁻¹) ^ d := by
  have hi : (radius width)⁻¹ ≤ 1 + (4 / 3 : ℝ) * width⁻¹ := by
    by_cases h : 3 * width / 4 ≤ 1
    · have he : (3 * width / 4)⁻¹ = (4 / 3 : ℝ) * width⁻¹ := by
        calc
          _ = 4 * (width⁻¹ * (3 : ℝ)⁻¹) := by
            simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
          _ = _ := by ring
      rw [radius, min_eq_left h, he]
      linarith
    · rw [radius, min_eq_right (le_of_not_ge h), inv_one]
      have hh := (inv_pos.mpr hw).le
      linarith
  have hp : ((radius width)⁻¹) ^ d ≤
      (1 + (4 / 3 : ℝ) * width⁻¹) ^ d :=
    pow_le_pow_left₀ (inv_nonneg.mpr (radius_pos hw).le) hi d
  unfold moment momentPrice
  rw [div_eq_mul_inv, ← inv_pow]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right (Real.exp_monotone (min_le_right _ _))
      (Nat.cast_nonneg _)) hp (pow_nonneg (inv_nonneg.mpr (radius_pos hw).le) _)
    (by positivity)

variable {S : List (Piece G n)} {p : BudgetPoint} {rankCap : ℕ}
    {width budget : ℝ}
    (H : ZeroAwareVacuumPackets S p rankCap width budget)

def factor (k : ℕ) : ℝ :=
  Next.Scheduling.Wages.startup G k p.power p.order * p.threshold ^ k *
    moment (Next.Scheduling.Wages.grade k p.power p.order) width *
      Real.exp (p.supportExponent * H.coverOffset)

def factorCeiling (k : ℕ) : ℝ :=
  Next.Scheduling.Wages.startup G k p.power p.order * p.threshold ^ k *
    (Real.exp 1 * (Next.Scheduling.Wages.grade k p.power p.order).factorial *
      (1 + (4 / 3 : ℝ) * width⁻¹) ^
        (Next.Scheduling.Wages.grade k p.power p.order)) * budget

private theorem factor_nonnegative (hw : 0 < width) (k : ℕ) :
    0 ≤ factor H k := by
  have hs : 0 ≤ Next.Scheduling.Wages.slotCost G p.power p.order 0 :=
    zero_le_one.trans (Next.Scheduling.Wages.slot_ge G p.power p.order 0)
  have ht := p.threshold_pos
  have hm := (moment_pos (Next.Scheduling.Wages.grade k p.power p.order) hw).le
  unfold factor Next.Scheduling.Wages.startup
  positivity

/-- The original cover cost is paid by its existing geometry budget. -/
theorem factor_bound (hw : 0 < width) (k : ℕ) :
    factor H k ≤ factorCeiling (G := G) (p := p) (width := width) (budget := budget) k := by
  let t := Next.Scheduling.Wages.startup G k p.power p.order * p.threshold ^ k
  let d := Next.Scheduling.Wages.grade k p.power p.order
  let Q := Real.exp 1 * d.factorial * (1 + (4 / 3 : ℝ) * width⁻¹) ^ d
  have hs : 0 ≤ Next.Scheduling.Wages.slotCost G p.power p.order 0 :=
    zero_le_one.trans (Next.Scheduling.Wages.slot_ge G p.power p.order 0)
  have ht : 0 ≤ t := by
    have hp := p.threshold_pos
    unfold t Next.Scheduling.Wages.startup
    positivity
  have hQ : 0 ≤ Q := by
    have hi := (inv_pos.mpr hw).le
    unfold Q
    positivity
  change t * moment d width * Real.exp (p.supportExponent * H.coverOffset) ≤
    t * Q * budget
  calc
    _ ≤ t * Q * Real.exp (p.supportExponent * H.coverOffset) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (moment_bound d hw) ht) (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left H.cover_cost (mul_nonneg ht hQ)

private theorem moment_absorb {k : ℕ} (a : Atom G k)
    (hw : 0 < width) (d : ℕ) :
    ((a.length : ℝ) + 1) ^ d * a.budget (width / 4) ≤
      moment d width * a.budget width := by
  have hz : 0 ≤ (a.length : ℝ) := by positivity
  have hp := spend d hw hz
  have hb : 0 ≤ a.budget (width / 4) := by
    unfold Atom.budget Atom.magnitude
    positivity
  calc
    _ ≤ (moment d width * Real.exp ((3 * width / 4) * a.length)) *
        a.budget (width / 4) :=
      mul_le_mul_of_nonneg_right (by simpa only [add_comm] using hp) hb
    _ = moment d width * a.budget width := by
      unfold Atom.budget
      calc
        _ = moment d width * a.magnitude *
            (Real.exp ((3 * width / 4) * a.length) *
             Real.exp ((width / 4) * a.length)) := by ring
        _ = _ := by
          rw [← Real.exp_add]
          rw [show (3 * width / 4) * (a.length : ℝ) +
              (width / 4) * a.length = width * a.length by ring]
          ring

private theorem derivative_row_le
    (hw : 0 < width) (a : Piece G n) (ha : a ∈ S) (i : ℕ) :
    p.mass (a.packet.labels i).support (Next.Scheduling.Wages.price p (H.atom a i)) ≤
      factor H a.rank * (H.atom a i).budget width := by
  let t := Next.Scheduling.Wages.startup G a.rank p.power p.order * p.threshold ^ a.rank
  let d := Next.Scheduling.Wages.grade a.rank p.power p.order
  have hs : 0 ≤ Next.Scheduling.Wages.slotCost G p.power p.order 0 :=
    zero_le_one.trans (Next.Scheduling.Wages.slot_ge G p.power p.order 0)
  have ht : 0 ≤ t := by
    have hp := p.threshold_pos
    unfold t Next.Scheduling.Wages.startup
    positivity
  have hl : 0 ≤ ((H.atom a i).length : ℝ) + 1 := by positivity
  have hc : 0 ≤ Real.exp (p.supportExponent * H.coverOffset) := (Real.exp_pos _).le
  calc
    _ = t * ((((H.atom a i).length : ℝ) + 1) ^ d *
        p.mass (a.packet.labels i).support (H.atom a i).magnitude) := by
      rw [Next.Scheduling.Wages.scan]
      unfold t d BudgetPoint.mass
      ring
    _ ≤ t * ((((H.atom a i).length : ℝ) + 1) ^ d *
        (Real.exp (p.supportExponent * H.coverOffset) *
          (H.atom a i).budget (width / 4))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (H.mass_budget a ha i) (pow_nonneg hl d)) ht
    _ = (t * Real.exp (p.supportExponent * H.coverOffset)) *
        ((((H.atom a i).length : ℝ) + 1) ^ d * (H.atom a i).budget (width / 4)) := by ring
    _ ≤ (t * Real.exp (p.supportExponent * H.coverOffset)) *
        (moment d width * (H.atom a i).budget width) :=
      mul_le_mul_of_nonneg_left (moment_absorb (H.atom a i) hw d) (mul_nonneg ht hc)
    _ = factor H a.rank * (H.atom a i).budget width := by
      unfold factor t d
      ring

/-- The complete original per-root row sum has the capped rank-specific price. -/
theorem derivative_budget (hw : 0 < width)
    (a : Piece G n) (ha : a ∈ S) (o : Site n) :
    SumBudget (fun i : ℕ => if (a.packet.labels i).site = o then
      p.mass (a.packet.labels i).support (Next.Scheduling.Wages.price p (H.atom a i))
      else 0) (factor H a.rank * H.pieceCost a) := by
  apply Cost.mono (Cost.scale (H.exponential a ha o)
    (factor H a.rank) (factor_nonnegative H hw a.rank))
  · intro i
    split
    · exact mul_nonneg (Real.exp_pos _).le
        (Next.Scheduling.Wages.total p (H.atom a i) (a.packet.labels i).site).1
    · exact le_rfl
  intro i
  by_cases hi : (a.packet.labels i).site = o
  · simp only [hi, if_true]
    exact derivative_row_le H hw a ha i
  · simp only [hi, if_false, mul_zero]
    exact le_rfl

def credit (a : Piece G n) : ℝ := factor H a.rank * H.pieceCost a

def bill (k : ℤ → ℝ) : ℝ :=
  (S.map (fun a => ‖weight k a‖ * credit H a)).sum

/-- The old Invoice contributes only its four structural fields. -/
theorem invoice (h : Render.permits S p) (hw : 0 < width)
    (a : Piece G n) (ha : a ∈ S) : a.packet.Invoice p (credit H a) := by
  have old := h a ha
  refine ⟨old.smooth, old.flat, old.null, old.moves, ?_⟩
  refine ⟨fun i => Next.Scheduling.Wages.price p (H.atom a i),
    fun i => H.canonical_price a ha i, fun o => ?_⟩
  exact derivative_budget H hw a ha o

private theorem repriced_permits (h : Render.permits S p) (hw : 0 < width) :
    Render.permits (repriceLayers (credit H) S) p := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact invoice H h hw b hb

private theorem dollars_repriced (k : ℤ → ℝ) :
    Render.dollars (fun a => ‖weight k a‖) (repriceLayers (credit H) S) = bill H k := by
  let c := credit H
  have hh (L : List (Piece G n)) :
      Render.dollars (fun a => ‖weight k a‖) (repriceLayers c L) =
        (L.map (fun a => ‖weight k a‖ * c a)).sum := by
    induction L with
    | nil => rfl
    | cons a L ih =>
        change ‖weight k a‖ * c a +
            Render.dollars (fun a => ‖weight k a‖) (repriceLayers c L) =
          ‖weight k a‖ * c a + (L.map (fun a => ‖weight k a‖ * c a)).sum
        rw [ih]
  exact hh S

theorem bill_nonnegative (h : Render.permits S p) (hw : 0 < width)
    (k : ℤ → ℝ) : 0 ≤ bill H k := by
  rw [← dollars_repriced H]
  exact Render.loose (repriced_permits H h hw)
    (fun a => ‖weight k a‖) (fun a => norm_nonneg _)

/-- The unchanged original full activities obtain the capped bill. -/
theorem valid (R : Rep G n) {S : List (Piece G n)}
    {rankCap : ℕ} {width budget d z : ℝ}
    (H : ZeroAwareVacuumPackets S R.p rankCap width budget)
    (h : Render.permits S R.p) (hw : 0 < width) (k : ℤ → ℝ)
    (hR : R.activities.Valid R.p d z) :
    (Render.append S R (weight k)).activities.Valid R.p (d + bill H k) z := by
  have hh := Render.addition (weight k) (repriced_permits H h hw) hR
  change (Render.adorn (weight k) R.activities
      (repriceLayers (credit H) S)).Valid R.p
      (d + Render.dollars (fun a => ‖weight k a‖)
        (repriceLayers (credit H) S)) z at hh
  rw [ZeroAwareIntrinsicRenderInvoice.adorn_unchanged, dollars_repriced H] at hh
  exact hh

end YM.Integration.ZeroAwareCappedRenderInvoice
end
