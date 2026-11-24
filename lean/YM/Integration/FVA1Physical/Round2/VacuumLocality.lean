import YM.Integration.FVA1Physical.CenteredVacuum

/-! An anchored response to a distant displacement of the physical small field.
The cost uses a single weighted Hessian row, even when the displacement
changes arbitrarily many distant coordinates. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Lattice Push Push.Uniform MSbar MSbar.Lis MSbar.Whisk
open scoped BigOperators Classical Topology

variable {σ : Type} [Fintype σ] {n : Side}

omit [Fintype σ] in
private theorem distance_weight (site : σ → Site n) {a : ℝ} (ha : 0 ≤ a) (s : ℕ)
    (i j : σ) {r : ℕ} (hr : r ≤ separation (site i) (site j)) :
    liftW a s r ≤ Measuring.swipe site a s [i, j] := by
  apply w_more (hr.trans (curve (x := site i) (y := site j) ?_ ?_)) ha s
  · simp [zone]
  · simp [zone]

/-- A rooted row of the Hessian controls the influence of an arbitrary distant
field displacement in supremum norm. The prefactor is independent of the
number of displaced coordinates. -/
theorem distant_hessian {site : σ → Site n} {a w B : ℝ} {s k : ℕ}
    {S : Set (Positions σ)} {F : Positions σ → ℝ}
    (J : JetTab site a s w S F 1 B) (hw : 0 < w) (ha : 0 ≤ a)
    {x : Positions σ} (hx : x ∈ S) (hf : ContDiffAt ℝ k F x) (hk : 2 ≤ k)
    (i : σ) (r : ℕ) (v : Positions σ)
    (far : ∀ j, v j ≠ 0 → r ≤ separation (site i) (site j)) :
    ‖fderiv ℝ (fun z => fderiv ℝ F z (bolt i)) x v‖ ≤
      ‖v‖ * (B / w^2) / liftW a s r := by
  let A := fderiv ℝ (fun z => fderiv ℝ F z (bolt i)) x
  let W := liftW a s r
  have hW : 0 < W := wpos .. 
  have coord (j : σ) : A (bolt j) = buoy F x [i,j] := by
    change roc F [bolt j, bolt i] x = roc F [bolt i, bolt j] x
    exact echo k hf _ _ (by simpa using hk) (List.Perm.swap _ _ [])
  have row := J.count hw x hx i
  change (∑ j : σ, |buoy F x [i,j]| * Measuring.swipe site a s [i,j]) ≤ B / w^2 at row
  apply (le_div_iff₀ hW).2
  calc
    ‖A v‖ * W ≤ (∑ j : σ, ‖v j‖ * |buoy F x [i,j]|) * W := by
      apply mul_le_mul_of_nonneg_right _ hW.le
      nth_rw 1 [spiral v]
      rw [map_sum]
      exact (norm_sum_le ..).trans_eq (Finset.sum_congr rfl fun j _ => by
        rw [map_smul, norm_smul, coord]; rfl)
    _ ≤ ∑ j : σ, ‖v‖ * (|buoy F x [i,j]| * Measuring.swipe site a s [i,j]) := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : v j = 0
      · simp only [hj, norm_zero, zero_mul]
        exact mul_nonneg (norm_nonneg _) (mul_nonneg (abs_nonneg _)
          (effect site a s ∅ [i,j]).le)
      · rw [mul_assoc]
        exact mul_le_mul (norm_le_pi_norm v j)
          (mul_le_mul_of_nonneg_left (distance_weight site ha s i j (far j hj)) (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) hW.le) (norm_nonneg _)
    _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left row (norm_nonneg _)

private theorem segment_price {f : ℝ → ℝ} {d : ℝ → ℝ} {M : ℝ}
    (hd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt f (d t) t)
    (bound : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖d t‖ ≤ M) : ‖f 1-f 0‖ ≤ M :=
  norm_image_sub_le_of_norm_deriv_le_segment_01' (f := f) (f' := d)
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (fun t ht => bound t (Set.Ico_subset_Icc_self ht))

/-- Changing the field outside radius r changes a held derivative by a
polynomial-exponential tail, with the price of the whole displacement paid once. -/
theorem distant_first_response {site : σ → Site n} {a w B : ℝ} {s k : ℕ}
    {S : Set (Positions σ)} {F : Positions σ → ℝ}
    (J : JetTab site a s w S F 1 B) (hw : 0 < w) (ha : 0 ≤ a)
    (hf : ∀ x ∈ S, ContDiffAt ℝ k F x) (hk : 2 ≤ k)
    (i : σ) (r : ℕ) (x v : Positions σ)
    (stay : ∀ t ∈ Set.Icc (0:ℝ) 1, x+t • v ∈ S)
    (far : ∀ j, v j ≠ 0 → r ≤ separation (site i) (site j)) :
    ‖fderiv ℝ F (x+v) (bolt i) - fderiv ℝ F x (bolt i)‖ ≤
      ‖v‖ * (B / w^2) / liftW a s r := by
  let D := fun z => fderiv ℝ F z (bolt i)
  have deriv (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      HasDerivAt (fun t : ℝ => D (x+t • v)) (fderiv ℝ D (x+t • v) v) t := by
    have sm := smooth k 1 [bolt i] (hf _ (stay t ht)) (by simpa using hk)
    change ContDiffAt ℝ (↑(1:ℕ)) D (x+t • v) at sm
    have inner : HasDerivAt (fun u : ℝ => x+u • v) v t := by
      simpa using ((hasDerivAt_id' t).smul_const v).const_add x
    exact (sm.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t inner
  have h := segment_price deriv (fun t ht => distant_hessian J hw ha
    (stay t ht) (hf _ (stay t ht)) hk i r v far)
  simpa only [D, one_smul, zero_smul, add_zero] using h

/-- A finite change at the root has an exponentially small sensitivity to
all fields outside the chosen radius, uniformly on the whole rectangle. -/
theorem distant_increment {site : σ → Site n} {a w B : ℝ} {s k : ℕ}
    {S : Set (Positions σ)} {F : Positions σ → ℝ}
    (J : JetTab site a s w S F 1 B) (hw : 0 < w) (ha : 0 ≤ a)
    (hf : ∀ x ∈ S, ContDiffAt ℝ k F x) (hk : 2 ≤ k)
    (i : σ) (r : ℕ) (x v : Positions σ) (h : ℝ)
    (stay : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ u ∈ Set.Icc (0:ℝ) 1,
      (x+t • (h • bolt i))+u • v ∈ S)
    (far : ∀ j, v j ≠ 0 → r ≤ separation (site i) (site j)) :
    ‖(F ((x+h • bolt i)+v) - F (x+v)) - (F (x+h • bolt i)-F x)‖ ≤
      ‖h‖ * (‖v‖ * (B / w^2) / liftW a s r) := by
  let y := fun t : ℝ => x+t • (h • bolt i)
  let L := fun t : ℝ => F (y t + v) - F (y t)
  let d := fun t : ℝ => h*(fderiv ℝ F (y t+v) (bolt i) - fderiv ℝ F (y t) (bolt i))
  have deriv (t : ℝ) (ht : t ∈ Set.Icc 0 1) : HasDerivAt L (d t) t := by
    have hy : HasDerivAt y (h • bolt i) t := by
      simpa [y] using ((hasDerivAt_id' t).smul_const (h • bolt i)).const_add x
    have h₀ : y t ∈ S := by simpa [y] using stay t ht 0 (by simp)
    have h₁ : y t + v ∈ S := by simpa [y] using stay t ht 1 (by simp)
    have left := ((hf _ h₁).differentiableAt (by exact_mod_cast (by omega : k ≠ 0))).hasFDerivAt.comp_hasDerivAt t (hy.add_const v)
    have right := ((hf _ h₀).differentiableAt (by exact_mod_cast (by omega : k ≠ 0))).hasFDerivAt.comp_hasDerivAt t hy
    simpa only [L, d, Function.comp_def, Pi.sub_def, map_smul, smul_eq_mul, mul_sub] using left.sub right
  have bound (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      ‖d t‖ ≤ ‖h‖ * (‖v‖ * (B / w^2) / liftW a s r) := by
    rw [show d t = _ from rfl, norm_mul]
    exact mul_le_mul_of_nonneg_left (distant_first_response J hw ha hf hk i r (y t) v
      (stay t ht) far) (norm_nonneg _)
  have H := segment_price deriv bound
  have ident : (F ((x+h • bolt i)+v) - F (x+v)) - (F (x+h • bolt i)-F x) = L 1-L 0 := by
    simp only [L,y,one_smul,zero_smul,add_zero]; ring
  rw [ident]; exact H

end YM.Integration.FVA1Physical.Round2
