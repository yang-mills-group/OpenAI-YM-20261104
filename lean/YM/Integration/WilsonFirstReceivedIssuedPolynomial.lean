import YM.Integration.WilsonFirstReceivedIssuedIncome
import YM.Integration.WilsonFirstReceivedRadialStencil

/-! Interpolation of the complete issued group observable. Its pupil rows
can have different true stencils and the same occupied roots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFirstReceivedIssuedPolynomial
open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn Exterior
open WilsonFirstReceivedRadialStencil WilsonFirstReceivedIssuedRowTaylor
open scoped BigOperators Classical

private def knots (d j : ℕ) : ℂ := node d j

private theorem distinct (d : ℕ) : Set.InjOn (knots d) (range (d + 1)) := by
  intro i _ j _ h
  have hij : node d i = node d j := Complex.ofReal_injective h
  exact_mod_cast (div_left_inj' (by positivity : (d + 1 : ℕ) ≠ (0 : ℝ))).mp hij

private theorem assemble {ι : Type} (p : ι → Polynomial ℂ) (d : ℕ)
    (deg : ∀ i, (p i).natDegree ≤ d)
    (nodal : ∀ j ≤ d, Summable fun i => (p i).eval (knots d j)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ d ∧ ∀ z : ℂ, (∑' i, (p i).eval z) = P.eval z := by
  let S := range (d + 1)
  let v := knots d
  let income (j : ℕ) := ∑' i, (p i).eval (v j)
  refine ⟨Lagrange.interpolate S v income, ?_, ?_⟩
  · apply Polynomial.natDegree_le_iff_degree_le.mpr
    simpa [S] using (Lagrange.degree_interpolate_le (r := income) (distinct d))
  · intro z
    let weight (j : ℕ) := (Lagrange.basis S v j).eval z
    have reconstruction (i : ι) : (p i).eval z = ∑ j ∈ S, (p i).eval (v j) * weight j := by
      have small : (p i).degree < (S.card : WithBot ℕ) := (p i).degree_le_natDegree.trans_lt (by
        change ((p i).natDegree : WithBot ℕ) < ((range (d + 1)).card : WithBot ℕ)
        rw [card_range]
        exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le (deg i)))
      conv_lhs => rw [Lagrange.eq_interpolate (distinct d) small]
      simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, weight, S, v]
    calc
      _ = ∑' i, ∑ j ∈ S, (p i).eval (v j) * weight j := tsum_congr reconstruction
      _ = ∑ j ∈ S, ∑' i, (p i).eval (v j) * weight j :=
        Summable.tsum_finsetSum fun j hj => (nodal j (Nat.le_of_lt_succ (mem_range.mp hj))).mul_right _
      _ = (Lagrange.interpolate S v income).eval z := by
        simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
          Polynomial.eval_C, tsum_mul_right, income, weight]

private theorem collect_series {ι : Type} (d : ℕ) (poly : ι → Polynomial ℂ)
    (degrees : ∀ i, (poly i).natDegree ≤ d) (f : ℝ → ι → ℂ) (raw : ℝ → ℂ)
    (physical : ∀ z, HasSum (f z) (raw z)) (κ : ℝ) (live : 0 < κ) (bill : ℝ → ℝ)
    (invoice : ∀ z : ℝ, SumBudget (fun i => κ * ‖f z i - (poly i).eval (z : ℂ)‖) (bill z)) :
    ∃ Y : Polynomial ℂ, Y.natDegree ≤ d ∧ ∀ z : ℝ, κ * ‖raw z - Y.eval (z : ℂ)‖ ≤ bill z := by
  let delta (z : ℝ) (i : ι) := f z i - (poly i).eval (z : ℂ)
  have norms (z : ℝ) : Summable fun i => ‖delta z i‖ := by
    simpa only [← mul_assoc, inv_mul_cancel₀ live.ne', one_mul, delta] using
      ((invoice z).2.1.mul_left κ⁻¹)
  have series (z : ℝ) : Summable fun i => (poly i).eval (z : ℂ) := by
    simpa only [delta, sub_sub_cancel] using (physical z).summable.sub (norms z).of_norm
  obtain ⟨Y, hY, all⟩ := assemble poly d degrees (fun j _ => series (node d j))
  refine ⟨Y, hY, ?_⟩
  intro z
  have signed : (∑' i, delta z i) = raw z - Y.eval (z : ℂ) := by
    rw [← all, ← (physical z).tsum_eq, ← (physical z).summable.tsum_sub (series z)]
  calc
    _ = κ * ‖∑' i, delta z i‖ := by rw [signed]
    _ ≤ κ * ∑' i, ‖delta z i‖ := mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (norms z)) live.le
    _ = ∑' i, κ * ‖delta z i‖ := tsum_mul_left.symm
    _ ≤ _ := (invoice z).2.2

variable {G : Gauge} {n : Side} {V α ι : Type} [DecidableEq V] {P : Passport n V} {R : Census V}

/-- The funded all-field sum is the actual before-test filing. A single
polynomial works simultaneously at every point of this physical ray. -/
theorem original (M : ι → Row P R G α) (w : V → ℝ) (hw : ∀ v, 0 < w v)
    {τ σ c : ℝ} (hτ : 0 ≤ τ) (hs : 0 < σ) (offer : Offers M w τ c)
    (paid : ∀ i, (M i).Budget) {K : ℕ} {p : V → ℕ} (due : Issues M σ K p)
    {g : ℝ} (hg : 0 < g) (hu : g ≤ 1) (u : α) (a : fieldDir G n 1)
    {A : ℝ} (ha : 0 ≤ A) (axis : ∀ e, ‖collect G a e‖ ≤ A)
    (bank : Config G n → Marker.Poly R)
    (quoted : ∀ U, HasSum (fun i => Poly.send (M i).mode ((M i).nominal g u U)) (bank U))
    (q : ℕ) (s : R.Mode) :
    let d := q + ∑ v ∈ s.val, p v
    ∃ Y : Polynomial ℂ, Y.natDegree ≤ d ∧ ∀ z : ℝ,
      Poly.toll w s * ‖(bank (Comparison.RG02.Integral.sample g (z • a))).part s - Y.eval (z : ℂ)‖ ≤
        ((2 * (G.colorScale * A) * |z| / σ) ^ (d + 1) * g ^ q) *
          ((s.val.image P.origin).card * c) := by
  intro d
  let κ := Poly.toll w s
  have live : 0 < κ := Poly.worth hw s
  let U (z : ℝ) := Comparison.RG02.Integral.sample g (z • a)
  let f (z : ℝ) (i : ι) := if (M i).mode = s then (M i).nominal g u (U z) else 0
  let poly (i : ι) := if (M i).mode = s then column (M i) g u (collect G a) d else 0
  let delta (z : ℝ) (i : ι) := f z i - (poly i).eval (z : ℂ)
  have physical (z : ℝ) : HasSum (f z) ((bank (U z)).part s) := by
    have all := Pi.hasSum.mp (quoted (U z)) s
    apply all.congr_fun
    intro i
    change _ = (Poly.send (M i).mode _).part s
    rw [Poly.part_send]
    by_cases h : (M i).mode = s <;> simp [f, h, eq_comm]
  have invoice (z : ℝ) : SumBudget (fun i => κ * ‖delta z i‖)
      (((2 * (G.colorScale * A) * |z| / σ) ^ (d + 1) * g ^ q) *
        ((s.val.image P.origin).card * c)) := by
    have quotedError := WilsonFirstReceivedIssuedIncome.filed M w hw hτ hs offer paid due hg hu
      u a ha axis q s z
    convert quotedError using 1
    funext i
    by_cases h : (M i).mode = s <;> simp [delta, f, poly, U, κ, d, h]
  have degrees (i : ι) : (poly i).natDegree ≤ d := by
    by_cases h : (M i).mode = s
    · simpa only [poly, if_pos h] using WilsonFirstReceivedIssuedRowTaylor.degree (M i) g u (collect G a) d
    · simp only [poly, if_neg h, Polynomial.natDegree_zero, Nat.zero_le]
  exact collect_series d poly degrees f (fun z => (bank (U z)).part s) physical κ live _ invoice

end YM.Integration.WilsonFirstReceivedIssuedPolynomial
