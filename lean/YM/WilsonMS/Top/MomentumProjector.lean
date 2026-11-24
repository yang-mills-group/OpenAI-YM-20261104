import YM.WilsonMS.Top.MomentumBlocks

/-! # Inverse relations for the literal momentum matrices -/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Position
open Function Finset Filter Set Matrix Complex Lattice
open MS MS.Orbit MS.Orbit.Cog MS.Koszul MS.Plane MS.Bare MS.Native
open MS.Book MS.Cylinder MS.Landau MS.Latch MS.City MS.Swirl MS.Swirl.Near MS.Tone
open MS.Momentum
open scoped Topology

variable (G : Gauge) (n : Side)
local notation "A'" => CA G n
local notation "L'" => LK G n
local notation "H'" => angularP G n
local notation "D'" => angularD G n
local notation "R'" => FFT.rev (Ax G) n
local notation "ν" => scaleZ n
local notation "Λ" => brightness n

section
variable {X Y Z : Type} [Fintype Z]

private lemma collapses (A : Matrix X (Z × Site n) ℂ) (B : Matrix (Z × Site n) Y ℂ) (x : X)
    (p : Site n) (h : ∀ z q, q ≠ p → A x (z, q) = 0) (y : Y) :
    (A * B) x y = ∑ z : Z, A x (z, p) * B (z, p) y := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single_of_mem p (mem_univ _)]
  intro j _ hj
  rw [h i j hj, zero_mul]
end

private lemma ld_mark (p q : Site n) (i j : G.ColorIndex) :
    (L' * D') (i, p) (j, q) = ∑ a : Axis, L' (i, p) ((a, i), -p) * D' ((a, i), -p) (j, q) := by
  rw [collapses n L' D' (i, p) (-p) (fun i q h => LF_off _ _ _ _ _ _ h), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single_of_mem i (mem_univ _)]
  intro k _ hk
  rw [L_matrix, if_neg (Ne.symm hk), zero_mul]

private lemma four_p (p : Site n) : ∑ i : Axis, (↑(wi n p i) : ℂ) * ↑(wi n p i) = muq n p := by
  simp [muq, Momentum.sq, pow_two]

lemma angular_left : L' * D' = FFT.exclude0 (G.ColorIndex) n := by
  classical
  ext ⟨i, p⟩ ⟨j, q⟩
  rw [ld_mark]
  by_cases hx : q = p
  swap
  · unfold FFT.exclude0
    split
    · simp_rw [DF_off G n p q _ _ hx, mul_zero, sum_const_zero]
    simp_rw [DF_off G n p q _ _ hx, mul_zero, sum_const_zero]
    exact (Matrix.one_apply_ne (fun h => hx (congr_arg Prod.snd h.symm))).symm
  subst q
  by_cases hv : i = j
  swap
  · simp_rw [D_matrix, if_neg hv, mul_zero, sum_const_zero]
    simp [FFT.exclude0, hv]
  subst j
  unfold FFT.exclude0
  simp only [Matrix.one_apply_eq]
  split
  next h =>
    change p = 0 at h
    subst p
    simp_rw [L_matrix, ite_true, mu_zero, div_zero, neg_zero, zero_mul, Finset.sum_const_zero]
  next h =>
    let W := wi n p
    let a := muq n p
    have H := wave_gap n p h
    have hΓ (i : Axis) : midPhase (-Coord p) i * midPhase (Coord p) i = 1 :=
      (mul_comm ..) |>.trans (mid_inv ..)
    simp_rw [L_matrix, D_matrix, ite_true]
    rw [show (∑ j : Axis, _) = (∑ j : Axis, (↑(wi n p j) : ℂ) * ↑(wi n p j)) / muq n p from ?_,
      four_p, div_self H]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    field_simp
    calc
      _ =
          (ν * Λ) * (midPhase (-Coord p) k * midPhase (Coord p) k) * (-Complex.I ^ 2) *
            ((↑(wi n p k) : ℂ) * ↑(wi n p k)) := by
        rw [Orbit.lightW]
        ring
      _ = _ := by
        rw [Complex.I_sq, hΓ k, Orbit.lightW]
        ring

private lemma p_prec (p : Site n) (i : Axis) :
    ∑ k : Axis, (↑(wi n p k) : ℂ) * (precision k i (wi n p) : ℂ) = 0 := by
  unfold precision Landau.delta
  push_cast
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  trans muq n p * ↑(wi n p i)
  · rw [Finset.sum_eq_single_of_mem i (mem_univ _)]
    simp
    rw [mul_comm]
    intro k _ hk
    simp [hk]
  rw [← four_p, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  exact _root_.mul_assoc ..

lemma angular_transverse : L' * R' * A' = 0 := by
  classical
  ext ⟨a, p⟩ ⟨⟨i, b⟩, q⟩
  rw [collapses n (L' * R') A' (a, p) p
      (fun k r h => by
        rw [FFT.mul_rev]
        exact LF_off G n p _ _ _ (fun v => h (neg_injective v)))]
  simp_rw [FFT.mul_rev]
  by_cases he : q = -p
  swap
  · refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [AF_off G n _ _ _ _ he, mul_zero]
  subst q
  simp_rw [Fintype.sum_prod_type]
  have hi j :
    (∑ b' : G.ColorIndex, L' (a, p) ((j, b'), -p) * A' ((j, b'), p) ((i, b), -p)) =
      L' (a, p) ((j, a), -p) * A' ((j, a), p) ((i, b), -p) := by
    rw [Finset.sum_eq_single_of_mem a (mem_univ _)]
    intro k _ hk
    rw [L_matrix, if_neg (Ne.symm hk), zero_mul]
  simp_rw [hi, L_matrix, A_matrix, ite_true]
  by_cases hx : a = b
  swap
  · simp [hx]
  simp_rw [show ∀ t : ℂ, (if a = b then t else 0) = t from fun _ => if_pos hx]
  let c := -ν * ν * midPhase (-Coord p) i / (muq n p) ^ 3 * Complex.I
  rw [show (∑ j : Axis, _) = c * (∑ j : Axis, (↑(wi n p j) : ℂ) * (precision j i (wi n p) : ℂ)) from
      ?_,
    p_prec, mul_zero]
  rfl
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold c
  linear_combination (norm := ring)
    (-ν * ν * midPhase (-Coord p) i * ((muq n p) ^ 3)⁻¹ * Complex.I * (↑(wi n p j) : ℂ) *
        (↑(precision j i (wi n p)) : ℂ)) *
      mid_inv j (Coord p)

private lemma ad_mark (p q : Site n) (i j : Axis) (a b : G.ColorIndex) :
    (A' * H') ((i, a), p) ((j, b), q) =
      ∑ k : Axis, A' ((i, a), p) ((k, a), -p) * H' ((k, a), -p) ((j, b), q) := by
  rw [collapses n A' H' ((i, a), p) (-p) (fun j r h => AF_off G n p r _ _ h), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single_of_mem a (mem_univ _)]
  intro x _ hx
  rw [A_matrix, if_neg (Ne.symm hx), zero_mul]

private lemma ad_value (p : Site n) (i j : Axis) (a : G.ColorIndex) :
    (A' * H') ((i, a), p) ((j, a), p) =
      midPhase (Coord p) i * midPhase (-Coord p) j * ((precision i j (wi n p) : ℝ) : ℂ) / muq n p := by
  rw [ad_mark]
  simp_rw [A_matrix, H_matrix, ite_true]
  by_cases hp : p = 0
  · subst p
    simp_rw [mu_zero, zero_pow (show 2 ≠ (0 : ℕ) from (by decide)), div_zero, zero_mul,
      Finset.sum_const_zero]
  let c := midPhase (Coord p) i * midPhase (-Coord p) j / (muq n p) ^ 2
  let W := wi n p
  have h := wave_gap n p hp
  have he (k : Axis) : midPhase (-Coord p) k * midPhase (Coord p) k = 1 :=
    (mul_comm ..) |>.trans (mid_inv ..)
  rw [show (∑ k : Axis, _) = c * ∑ k : Axis, (precision i k W : ℂ) * (precision k j W : ℂ) from ?_]
  swap
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold c W
    rw [show
        ν * midPhase _ i * midPhase _ k * (precision i k (wi n p) : ℂ) / muq n p ^ 2 *
            (Λ * midPhase _ k * midPhase _ j * (precision k j (wi n p) : ℂ)) =
          ν * Λ * (midPhase (-Coord p) k * midPhase (Coord p) k) *
            (c * ((precision i k W : ℂ) * (precision k j W : ℂ)))
        from ?_,
      lightW, he, one_mul, one_mul]
    unfold c W
    ring
  obtain ht := congr_arg Complex.ofReal (Landau.k_times i j W)
  push_cast at ht
  rw [ht]
  change _ * (muq n p * _) = _
  unfold W c
  field_simp

private lemma dl_mark (p q : Site n) (i j : Axis) (a b : G.ColorIndex) :
    (R' * (D' * L') * R') ((i, a), p) ((j, b), q) = D' ((i, a), -p) (a, p) * L' (a, p) ((j, b), -q) := by
  rw [FFT.mul_rev, FFT.rev_mul]
  dsimp only
  rw [collapses n D' L' ((i, a), -p) p (fun j r h => DF_off G n p r _ _ h),
    Finset.sum_eq_single_of_mem a (mem_univ _)]
  intro j _ hj
  rw [D_matrix, if_neg (Ne.symm hj), zero_mul]

lemma angular_inverse : A' * H' + R' * (D' * L') * R' = FFT.exclude0 (Ax G) n := by
  classical
  ext ⟨⟨i, a⟩, p⟩ ⟨⟨j, b⟩, q⟩
  rw [Matrix.add_apply, dl_mark]
  by_cases h : q = p
  swap
  · rw [ad_mark]
    simp_rw [HF_off G n p q _ _ h, mul_zero, Finset.sum_const_zero]
    rw [LF_off G n p _ _ _ (fun hz => h (neg_injective hz)), mul_zero, add_zero]
    simp [FFT.exclude0, Ne.symm h]
  subst q
  by_cases ht : a = b
  swap
  · rw [ad_mark]
    simp_rw [H_matrix, if_neg ht, mul_zero, Finset.sum_const_zero]
    rw [L_matrix, if_neg ht, mul_zero, add_zero]
    simp [FFT.exclude0, ht]
  subst b
  rw [ad_value, D_matrix, L_matrix, if_pos rfl]
  by_cases hp : p = 0
  · subst p
    simp_rw [mu_zero]
    simp [FFT.exclude0]
  rw [if_pos rfl]
  have H := wave_gap n p hp
  rw [show
      _ + _ =
        midPhase (Coord p) i * midPhase (-Coord p) j / muq n p *
          ((precision i j (wi n p) : ℂ) + (↑(wi n p i) : ℂ) * ↑(wi n p j))
      from ?_]
  · rw [Landau.precision]
    push_cast
    rw [sub_add_cancel]
    unfold Landau.delta
    by_cases hh : i = j
    swap
    · simp [hh, FFT.exclude0]
    subst j
    rw [if_pos rfl, mid_inv]
    change 1 / muq n p * muq n p = _
    rw [div_mul_cancel₀ _ H]
    simp [FFT.exclude0, hp]
  let d :=
    Λ * midPhase (Coord p) i * (Complex.I * ↑(wi n p i)) *
      (-(ν * midPhase (-Coord p) j * (Complex.I * ↑(wi n p j)) / muq n p))
  let u := midPhase (Coord p) i * midPhase (-Coord p) j / muq n p * ((↑(wi n p i) : ℂ) * ↑(wi n p j))
  have hh : d = u := by
    unfold d
    rw [show Λ * _ * _ * _ = (-Complex.I ^ 2) * (ν * Λ) * u from ?_, lightW, Complex.I_sq]
    · ring
    unfold u
    ring
  rw [show Λ * _ * _ * _ = _ from hh]
  unfold u
  ring
end YM.WilsonMS.Position
