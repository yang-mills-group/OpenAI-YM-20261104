import YM.Integration.FVA1Physical.Round2.VacuumLocality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Localize an actual smooth discrepancy without making a choice of an
ordering of the lattice. The radial fundamental theorem of calculus assigns
one term to each coordinate. Restricting its field to a ball gives a local
representative, and the weighted Hessian bounds the discarded part. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Lattice Push Push.Uniform MSbar MSbar.Lis MSbar.Whisk MeasureTheory
open scoped BigOperators Classical Topology Interval

variable {σ : Type} [Fintype σ] {n : Side}

/-- The share of a field increment attached to coordinate i. -/
def radialShare (F : Positions σ → ℝ) (i : σ) (x : Positions σ) : ℝ :=
  ∫ t in (0:ℝ)..1, x i * fderiv ℝ F (t • x) (bolt i)

/-- Restrict coordinates to the radius-r ball about i. -/
def nearField (site : σ → Site n) (i : σ) (r : ℕ) (x : Positions σ) : Positions σ :=
  fun j => if separation (site i) (site j) ≤ r then x j else 0

theorem nearField_norm (site : σ → Site n) (i : σ) (r : ℕ) (x : Positions σ) :
    ‖nearField site i r x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro j
  by_cases hj : separation (site i) (site j) ≤ r
  · simpa [nearField,hj] using norm_le_pi_norm x j
  · simp [nearField,hj]

omit [Fintype σ] in
theorem radialShare_local (site : σ → Site n) (i : σ) (r : ℕ)
    (F : Positions σ → ℝ) {x y : Positions σ}
    (same : ∀ j, separation (site i) (site j) ≤ r → x j = y j) :
    radialShare F i (nearField site i r x) = radialShare F i (nearField site i r y) := by
  congr 1
  funext j
  by_cases hj : separation (site i) (site j) ≤ r <;> simp [nearField,hj,same]

private theorem scaled_mem {w : ℝ} {x : Positions σ} (hx : x ∈ Metric.closedBall 0 w)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : t • x ∈ Metric.closedBall 0 w := by
  apply mem_closedBall_zero_iff.mpr
  rw [norm_smul, Real.norm_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg x) ht.2).trans (mem_closedBall_zero_iff.mp hx)

private theorem radial_integrable {w : ℝ} {k : ℕ} {F : Positions σ → ℝ}
    (hf : ∀ x ∈ Metric.closedBall 0 w, ContDiffAt ℝ k F x) (hk : 1 ≤ k)
    {x : Positions σ} (hx : x ∈ Metric.closedBall 0 w) (i : σ) :
    IntervalIntegrable (fun t : ℝ => x i * fderiv ℝ F (t • x) (bolt i)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)]
  intro t ht
  have sm := smooth k 0 [bolt i] (hf _ (scaled_mem hx ht)) (by simpa using hk)
  have c : ContinuousAt (fun y => fderiv ℝ F y (bolt i)) (t • x) := sm.continuousAt
  have comp : ContinuousAt ((fun z : Positions σ => fderiv ℝ F z (bolt i)) ∘ (fun u : ℝ => u • x)) t :=
    c.comp (f := fun u : ℝ => u • x) (x := t) (by fun_prop)
  exact (continuousAt_const.mul comp).continuousWithinAt

/-- The exact full scalar component is the sum of its rooted field shares,
up to its actual value at zero. -/
theorem radialShare_sum {w : ℝ} {k : ℕ} {F : Positions σ → ℝ}
    (hf : ∀ x ∈ Metric.closedBall 0 w, ContDiffAt ℝ k F x) (hk : 1 ≤ k)
    {x : Positions σ} (hx : x ∈ Metric.closedBall 0 w) :
    ∑ i, radialShare F i x = F x-F 0 := by
  let c := fun (i : σ) (t : ℝ) => x i * fderiv ℝ F (t • x) (bolt i)
  have hc (t : ℝ) : fderiv ℝ F (t • x) x = ∑ i, c i t := by
    nth_rw 2 [spiral x]
    simp only [map_sum, map_smul, smul_eq_mul, c]
  have hi (i : σ) : IntervalIntegrable (c i) volume 0 1 := radial_integrable hf hk hx i
  have hd (t : ℝ) (ht : t ∈ Set.uIcc (0:ℝ) 1) :
      HasDerivAt (fun u : ℝ => F (u • x)) (∑ i, c i t) t := by
    rw [← hc]
    rw [Set.uIcc_of_le zero_le_one] at ht
    have inner : HasDerivAt (fun u : ℝ => u • x) x t := by simpa using (hasDerivAt_id' t).smul_const x
    exact ((hf _ (scaled_mem hx ht)).differentiableAt (by exact_mod_cast (by omega : k ≠ 0))).hasFDerivAt.comp_hasDerivAt t inner
  have isum : IntervalIntegrable (fun t => ∑ i, c i t) volume 0 1 := by
    have se : (fun t => ∑ i, c i t) = ∑ i, c i := by funext t; rw [Finset.sum_apply]
    rw [se]
    exact IntervalIntegrable.sum (s := Finset.univ) (fun i _ => hi i)
  have result := intervalIntegral.integral_eq_sub_of_hasDerivAt hd isum
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)] at result
  simpa only [radialShare,c,one_smul,zero_smul] using result

/-- Price the replacement of the full rooted share by its local representative
on an arbitrary torus. All coordinates outside the ball may change together. -/
theorem radialShare_tail {site : σ → Site n} {a w B : ℝ} {s k : ℕ}
    {F : Positions σ → ℝ}
    (J : JetTab site a s w (Metric.closedBall 0 w) F 1 B)
    (hw : 0 < w) (ha : 0 ≤ a) (hf : ∀ x ∈ Metric.closedBall 0 w, ContDiffAt ℝ k F x)
    (hk : 2 ≤ k) (i : σ) (r : ℕ) {x : Positions σ} (hx : x ∈ Metric.closedBall 0 w) :
    ‖radialShare F i x - radialShare F i (nearField site i r x)‖ ≤
      ‖x i‖ * (‖x‖ * (B / w^2) / liftW a s (r+1)) := by
  let y := nearField site i r x
  have hy : y ∈ Metric.closedBall 0 w :=
    mem_closedBall_zero_iff.2 ((nearField_norm site i r x).trans (mem_closedBall_zero_iff.1 hx))
  have root : y i = x i := by simp [y,nearField]
  have nonneg : 0 ≤ B / w^2 := div_nonneg J.zeroP (sq_nonneg w)
  have tail (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      ‖fderiv ℝ F (t • x) (bolt i)- fderiv ℝ F (t • y) (bolt i)‖ ≤
        ‖x‖ * (B/w^2) / liftW a s (r+1) := by
    let v := t • (x-y)
    have diff : ‖x-y‖ ≤ ‖x‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2; intro j
      by_cases h : separation (site i) (site j) ≤ r
      · simp [Pi.sub_apply,y,nearField,h]
      · simpa [Pi.sub_apply,y,nearField,h] using norm_le_pi_norm x j
    have hv : ‖v‖ ≤ ‖x‖ := by
      dsimp only [v]; rw [norm_smul,Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans diff
    have far (j : σ) (hj : v j ≠ 0) : r+1 ≤ separation (site i) (site j) := by
      by_contra! near
      have h : separation (site i) (site j) ≤ r := by omega
      simp [v,y,nearField,h] at hj
    have finish : t • y + v = t • x := by simp [v,smul_sub]
    have stay (u : ℝ) (hu : u ∈ Set.Icc 0 1) : t • y + u • v ∈ Metric.closedBall 0 w := by
      have H := (convex_closedBall (0 : Positions σ) w)
        (scaled_mem hy ht) (scaled_mem hx ht) (sub_nonneg.mpr hu.2) hu.1 (sub_add_cancel 1 u)
      convert H using 1
      dsimp [v]; rw [smul_sub, smul_sub, sub_smul, one_smul]; abel
    have estimate := distant_first_response J hw ha hf hk i (r+1) (t • y) v stay far
    rw [finish] at estimate
    exact estimate.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv nonneg) (wpos ..).le)
  unfold radialShare
  rw [← intervalIntegral.integral_sub (radial_integrable hf (by omega) hx i)
    (radial_integrable hf (by omega) hy i)]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := ‖x i‖ * (‖x‖ * (B / w^2) / liftW a s (r+1))) ?_).trans_eq
  · simp
  intro t ht
  rw [Set.uIoc_of_le zero_le_one] at ht
  change ‖x i * _ - y i * _‖ ≤ _
  rw [root, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (tail t (Set.Ioc_subset_Icc_self ht)) (norm_nonneg _)

end YM.Integration.FVA1Physical.Round2
