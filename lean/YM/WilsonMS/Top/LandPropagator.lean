import YM.WilsonMS.Top.RootLift

/-! # Read back the transverse conditions at the based root -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Quo
open Function Filter Set Finset Matrix Complex Lattice XSpace
open MS MS.Orbit MS.Bare MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.Native Root Position Darboux
open scoped Topology ContDiff Matrix.Norms.Frobenius

variable {P : Period} (T : P.Tree) (G : Gauge)
local notation "N" => P.side
local notation "B'" => liftN T G
local notation "T'" => SiteField G P.side
local notation "V'" => GaugeField G P.side
local notation "J'" => liftJ P G
local notation "M'" => averageM T G
local notation "L'" => landL T G
local notation "L0" => straightL G P.side
local notation "A0" => straightA G P.side
local notation "D" => fullD G P.side
local notation "H" => fullH G P.side
local notation "R" => gradientM T G
local notation "F" => precisionM T G
local notation "Y" => Root.LogSpace G P
local notation "V" => Native.Chart.City G P.Sites
local notation "θE" => flipE G P.side

lemma links_basis (i : LinksI G P) :
    liftedA P G (priv i) = ∑ x : T', ((J' x i).re) • priv (linkEquiv G N x) := by
  nth_rw 1 [← Native.frame (liftedA P G (Native.priv i))]
  rw [← Equiv.sum_comp (linkEquiv G N)]
  apply Finset.sum_congr rfl
  intro j _
  rw [expands_basis, ofReal_re]
  rfl

/-- Hessian of the based action as an actual **half** pullback. This explains
the doubling in the covariant propagator. -/
lemma projects_price : F = ((2 : ℂ)⁻¹) • (J'ᵀ * H * J') := by
  let Y1 := coordinates T G
  let u := Native.Chart.rent (G := G) (Native.Chart.drive N)
  let γ := liftedA P G
  let g := LinearMap.toContinuousLinearMap γ
  let y := Y1.e0
  let a₁ (i : T') := Native.priv (linkEquiv G N i)
  let b₁ (i : LinksI G P) : LogSpace G P := Native.priv i
  have h : germ u := Native.Chart.rent_s _
  have ht : germ (u ∘ g) :=
    ContDiffAt.comp (f := ⇑g) 0
      (by
        rw [map_zero]
        exact h)
      g.contDiff.contDiffAt
  have hx : energyE P G = ((2 : ℝ)⁻¹) • (u ∘ g) :=
    funext fun i => (cover_exp G i).trans (div_eq_inv_mul ..)
  have hy : ink b₁ (u ∘ g) = specialize J' (ink a₁ u) := by
    rw [ink_ctrl_one _ _ h]
    rw [show specialize J' (ink a₁ u) = _ from specialize_shade J' (region.symm (ink a₁ u))]
    have he : J'ᵀ = (Matrix.of fun i j => ((J' j i).re : ℂ)) := by
      ext x y
      rw [transpose_apply, of_apply, expands_basis, Complex.ofReal_re]
    rw [he]
    refine scale_pos a₁ _ (fun i j => (J' j i).re) (fun _ => links_basis ..) h
  let Q (i j : T') := ink a₁ u [i, j]
  have hu i j : H i j = -Q i j := rfl
  ext i j
  have ha : F i j = -ink b₁ (energyE P G) [i, j] := rfl
  rw [ha, hx, ink_smul b₁ ht, Pi.smul_apply, hy]
  have hg : specialize J' (ink a₁ u) [i, j] = -(J'ᵀ * H * J' : Matrix _ _ ℂ) i j := by
    change Koszul.D j (Koszul.D i (specialize J' _)) [] = _
    simp only [specialize_deriv, map_sum, map_smul, Finset.smul_sum, Finset.sum_apply, Pi.smul_apply,
      specialize_nil, smul_eq_mul]
    simp_rw [at_D, Matrix.mul_apply, hu, Finset.sum_mul, transpose_apply, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    unfold Q
    ring
  rw [hg, Complex.ofReal_inv, Complex.ofReal_ofNat, Matrix.smul_apply, smul_neg, neg_neg]

lemma gauge_kind (x : P.Sites) (i : Axis) (k : G.ColorIndex) (f : V' → ℂ) :
    (D *ᵥ f) ((i, k), x) = f (k, x + step i) - f (k, x) := by
  let Q (y : P.Sites) (z : V') := (↑(priv (siteEquiv G N z) y k) : ℂ)
  have h (y : P.Sites) : f (k, y) = ∑ z : V', Q y z * f z := by
    rw [Finset.sum_eq_single_of_mem (k, y) (mem_univ _)]
    · unfold Q siteEquiv
      simp [Native.priv, baseC]
    rintro ⟨c, v⟩ _ hc
    unfold Q
    by_cases hp : y = v
    swap
    · simp [Native.priv, siteEquiv, hp]
    have hv : k ≠ c := by
      intro h
      exact hc (Prod.ext h.symm hp.symm)
    subst y
    simp [Native.priv, baseC, siteEquiv, hv]
  rw [h, h, ← Finset.sum_sub_distrib]
  change (∑ j : V', D ((i, k), x) j * f j) = _
  apply Finset.sum_congr rfl
  intro j _
  rw [gradFull]
  push_cast
  rw [_root_.sub_mul]

lemma gauge_lift : J' * R = D * B' := by
  ext ⟨⟨j, k⟩, x⟩ y
  rw [show (D * B' : Matrix _ _ ℂ) _ _ = _ from gauge_kind G x j k (fun i => B' i y)]
  let p := ((j, k), x)
  let f (x : P.Vertex) (i : G.ColorIndex) := ((↑(based T G (priv y) x i)) : ℂ)
  change (J' * R : Matrix _ _ ℂ) p y = f (P.vertex (p.2 + step p.1.1)) p.1.2 - f (P.vertex p.2) p.1.2
  generalize p = z
  have hx (s : LinksI G P) : R s y = f (P.dst s.1) s.2 - f (P.src s.1) s.2 := by
    rw [gradient_def]
    push_cast
    rfl
  rcases covered G z with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · rw [← row_inclusion (chosen P G) (J' * R), ← Matrix.mul_assoc, liftJ, Matrix.mul_sub,
      inclusion_mul (chosen_inj P G), inclusion_cross (separate P G), sub_zero, Matrix.one_mul, hx]
    rfl
  rw [← row_inclusion (inverted P G) (J' * R), ← Matrix.mul_assoc, liftJ, Matrix.mul_sub,
    inclusion_cross (fun i j => Ne.symm (separate P G j i)), inclusion_mul (inverted_inj P G),
    zero_sub, Matrix.neg_mul, Matrix.one_mul, Matrix.neg_apply, hx]
  let e := z.1
  change
    -(f (P.dst e) _ - f (P.src e) _) =
      f (P.vertex ((P.reflect e.val).1 + step e.val.2)) _ - f (P.vertex (P.reflect e.val).1) _
  rw [P.reflect_dest, P.reflect_base, P.vertex_neg, P.vertex_neg, neg_sub]
  rfl

lemma harmonic_fix : D * M' = J' * R := by
  unfold averageM
  rw [← Matrix.mul_assoc, Matrix.mul_sub, Position.grad_zero_mode, Matrix.mul_one, sub_zero,
    gauge_lift]

def landC (P : Period) (G : Gauge) : Matrix (LinksI G P) (LinksI G P) ℂ :=
  ((2 : ℂ)⁻¹) • ((liftJ P G)ᵀ * straightA G P.side * liftJ P G)
local notation "C'" => landC P G

lemma land_pull : J' * C' = A0 * J' := by
  unfold landC
  rw [Matrix.mul_smul, ← Matrix.mul_assoc J', ← Matrix.mul_assoc J', projected, Matrix.add_mul,
    Position.mirrors, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, mirror_lift]
  module

lemma gram_image : A0 * (1 + θE) = J' * C' * J'ᵀ := by rw [← projected, land_pull, Matrix.mul_assoc]

lemma longitudinal_image : (L0 * (1 + θE) : Matrix _ _ ℂ) = M' * L' * J'ᵀ := by
  rw [← projected, land_eq, Matrix.mul_assoc]

lemma perpendicular : L' * C' = 0 := by
  apply authority T G
  rw [← Matrix.mul_assoc, land_eq, Matrix.mul_assoc, land_pull, ← Matrix.mul_assoc,
    Position.straight_transverse, Matrix.zero_mul, Matrix.mul_zero]

/-- Main matrix check. Based LPT has no harmonic gauge field; `J'` is
the site-field lift. Ghosts on the gauge slice lift (also subtract their
constant part). Their induced matrices from the MS
momentum-zero-deleted kernel solve the Splitting equations. Uses the nonzero momentum
identities and proves accounting even at
the exceptional momenta exactly; no assumption of a cover formula for the
position covariance. -/
lemma split : Darboux.Splitting F R C' L'
    where
  symmC := by
    unfold landC
    rw [transpose_smul, transpose_mul, transpose_mul, transpose_transpose, Position.sym_C,
      Matrix.mul_assoc]
  symmH := precision_symm ..
  left := by
    apply authority T G
    let p := FFT.originP G.ColorIndex P.side
    have ht : M' * (L' * R) = M' := by
      rw [← Matrix.mul_assoc, land_eq, Matrix.mul_assoc, ← harmonic_fix, ← Matrix.mul_assoc,
        Position.straight_left]
      have hz : p * M' = 0 := by
        unfold averageM
        rw [← Matrix.mul_assoc, Matrix.mul_sub]
        rw [show p * p = p from ?_, Matrix.mul_one, sub_self, Matrix.zero_mul]
        refine constants_mean _ _ (fun x y h => ?_)
        funext i
        rcases x with ⟨x, u⟩
        rcases y with ⟨y, v⟩
        dsimp only at h
        unfold p
        rcases i with ⟨i, a⟩
        rw [h, FFT.origin_cell, FFT.origin_cell]
      rw [Matrix.sub_mul, hz, Matrix.one_mul, sub_zero]
    rw [ht, Matrix.mul_one]
  inverse := by
    apply cancelJ G
    let E := FFT.originP (Ax G) P.side
    have he : J' * R * L' = D * L0 * J' := by
      rw [← harmonic_fix, Matrix.mul_assoc, land_eq, Matrix.mul_assoc]
    have hx : J' * C' * F = ((2 : ℂ)⁻¹) • ((1 + θE) * (J' - J' * (R * L'))) := by
      rw [land_pull, projects_price, Matrix.mul_smul]
      congr 1
      calc
        _ = A0 * (1 + θE) * (H * J') := by
          rw [← projected]
          simp only [← Matrix.mul_assoc]
        _ = (1 + θE) * (A0 * H * J') := by
          rw [show A0 * (1 + θE) = (1 + θE) * A0 by
              rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Position.mirrors]]
          simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [show A0 * H = 1 - E - D * L0 from eq_sub_of_add_eq (Position.straight_inverse ..),
            Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, show E * J' = 0 from no_zero G, sub_zero,
            ← he, Matrix.mul_assoc]
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hx, Matrix.mul_one, Matrix.mul_sub, ←
      Matrix.mul_assoc (1 + θE), Matrix.add_mul (1 : Matrix _ _ ℂ), Matrix.one_mul, mirror_lift,
      Matrix.add_mul]
    module
end YM.WilsonMS.Quo
