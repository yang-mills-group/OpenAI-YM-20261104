import YM.CellFourier.Mesh
import YM.Integration.MSFixedRatioSignedReading

/-! Lift the actual finite two-wave error to arbitrary real link and color
directions by inverse Fourier expansion on the full finite native torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSFixedRatioFourierLifting

open Function Finset Lattice Exterior RG Wilson Precision Bloch Laurent
open Comparison.RG02 Comparison.RG02.Assembly Marker
open scoped Topology ContDiff Classical BigOperators

variable {G : Gauge} {c : Side}

def size (u : fieldDir G c 1) : ℝ :=
  ∑ x : Site c, ∑ a : TypeFace 1, ∑ j : G.ColorIndex, |u (x,a) j|

theorem size_nonneg (u : fieldDir G c 1) : 0 ≤ size u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

def amplitude (u : fieldDir G c 1) (p : Site c) (a : TypeFace 1) (j : G.ColorIndex) : ℂ :=
  ∑ x : Site c, (cell p x)⁻¹ * (u (x,a) j : ℂ)

def normalized (u : fieldDir G c 1) (p : Site c) (a : TypeFace 1) (j : G.ColorIndex) : ℂ :=
  (((size u)⁻¹ : ℝ) : ℂ) * amplitude u p a j

private theorem cell_unit (p x : Site c) : ‖cell p x‖ = 1 :=
  mode_real (mon p) (lift x) (real_frequency p)

theorem bounded (u : fieldDir G c 1) (p : Site c) (a : TypeFace 1) (j : G.ColorIndex) :
    ‖amplitude u p a j‖ ≤ size u := by
  apply (norm_sum_le ..).trans
  unfold size
  apply Finset.sum_le_sum
  intro x _
  rw [norm_mul, norm_inv, cell_unit, inv_one, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (Finset.single_le_sum (f := fun j => |u (x,a) j|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun b : TypeFace 1 => ∑ j, |u (x,b) j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a))

theorem normalized_bound (u : fieldDir G c 1) (p : Site c)
    (a : TypeFace 1) (j : G.ColorIndex) : ‖normalized u p a j‖ ≤ 1 := by
  by_cases hz : size u = 0
  · simp [normalized, hz]
  have hp := lt_of_le_of_ne (size_nonneg u) (Ne.symm hz)
  rw [normalized, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
  exact (mul_le_mul_of_nonneg_left (bounded u p a j) (inv_nonneg.mpr hp.le)).trans_eq
    (inv_mul_cancel₀ hz)

private theorem orthogonal_sites (x y : Site c) :
    (∑ p : Site c, cell p x*(cell p y)⁻¹) =
      if x=y then (Fintype.card (Site c) : ℂ) else 0 := by
  calc (∑ p : Site c, cell p x*(cell p y)⁻¹) =
      ∑ p : Site c, cell x p*(cell y p)⁻¹ := Finset.sum_congr rfl fun p _ => by
        rw [cell_duality p x, cell_duality p y]
    _ = _ := by rw [orthogonal, site_card]; push_cast; rfl

private theorem raw (u : fieldDir G c 1) :
    (∑ p : Site c, Precision.wave p (amplitude u p)) =
      (Fintype.card (Site c) : ℝ) • u := by
  funext z
  ext j
  have h (x : Site c) (a : TypeFace 1) :
      (∑ p : Site c, cell p x*amplitude u p a j) =
        (Fintype.card (Site c) : ℂ)*(u (x,a) j : ℂ) := by
    calc (∑ p : Site c, cell p x*amplitude u p a j) =
        ∑ y : Site c, (∑ p : Site c, cell p x*(cell p y)⁻¹)*(u (y,a) j : ℂ) := by
          unfold amplitude
          simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
          exact Finset.sum_comm
      _ = _ := by simp_rw [orthogonal_sites]; simp [ite_mul]
  have hsum : (∑ p : Site c, Precision.wave p (amplitude u p)) z j =
      ∑ p : Site c, Precision.wave p (amplitude u p) z j := by
    rw [Finset.sum_apply]
    exact map_sum (EuclideanSpace.proj j : G.Color →L[ℝ] ℝ) _ _
  rw [hsum]
  change (∑ p : Site c, (cell p z.1*amplitude u p z.2 j).re) =
    (Fintype.card (Site c):ℝ)*(u z j)
  have hr := congrArg Complex.re (h z.1 z.2)
  simpa only [Complex.re_sum,
    Complex.ofReal_re, Complex.natCast_re, Complex.mul_re, Complex.natCast_im,
    Complex.ofReal_im, mul_zero, sub_zero, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul] using hr

private theorem scale_wave (t : ℝ) (p : Site c) (a : TypeFace 1 → G.ColorIndex → ℂ) :
    Precision.wave p (fun i j => (t:ℂ)*a i j) = t • Precision.wave p a := by
  funext x
  ext j
  change (cell p x.1*((t:ℂ)*a x.2 j)).re = t*(cell p x.1*a x.2 j).re
  rw [mul_left_comm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem restored (u : fieldDir G c 1) (p : Site c) :
    size u • Precision.wave p (normalized u p) = Precision.wave p (amplitude u p) := by
  rw [show normalized u p = (fun i j => (((size u)⁻¹ : ℝ):ℂ)*amplitude u p i j) from rfl,
    scale_wave, smul_smul]
  by_cases hz : size u = 0
  · have hzero (i j) : amplitude u p i j = 0 :=
      norm_le_zero_iff.mp ((bounded u p i j).trans_eq hz)
    simp only [hz, zero_mul, zero_smul]
    funext x
    ext j
    change 0 = (cell p x.1 * amplitude u p x.2 j).re
    rw [hzero x.2 j, mul_zero, Complex.zero_re]
  rw [mul_inv_cancel₀ hz, one_smul]

theorem invert (u : fieldDir G c 1) :
    u = ∑ p : Site c, (size u/(Fintype.card (Site c):ℝ)) • Precision.wave p (normalized u p) := by
  let v : ℝ := Fintype.card (Site c)
  have hv : v ≠ 0 := by
    change (Fintype.card (Site c) : ℝ) ≠ 0
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Site c) ≠ 0)
  calc u = v⁻¹ • (v • u) := by rw [smul_smul, inv_mul_cancel₀ hv, one_smul]
       _ = v⁻¹ • ∑ p : Site c, size u • Precision.wave p (normalized u p) := by
         rw [← raw u]
         simp_rw [restored]
       _ = _ := by
         rw [Finset.smul_sum]
         apply Finset.sum_congr rfl
         intro p _
         rw [smul_smul, div_eq_mul_inv, mul_comm]

/-- The normalized Fourier average cancels the two cardinal factors. The
bound holds on every independent real edge and color direction. -/
theorem lift (D : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => fieldDir G c 1) ℝ)
    (E : ℝ) (h : ∀ (p q : Site c) (σ τ : TypeFace 1 → G.ColorIndex → ℂ),
      (∀ i j, ‖σ i j‖ ≤ 1) → (∀ i j, ‖τ i j‖ ≤ 1) →
      |D ![Precision.wave p σ, Precision.wave q τ]| ≤ E)
    (u v : fieldDir G c 1) : |D ![u,v]| ≤ E*size u*size v := by
  let d : ℝ := Fintype.card (Site c)
  have hd : 0 < d := by
    change (0 : ℝ) < Fintype.card (Site c)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Site c))
  let T : Fin 2 → fieldDir G c 1 := ![u,v]
  let w (j : Fin 2) := size (T j)/d
  let b (j : Fin 2) (p : Site c) := Precision.wave p (normalized (T j) p)
  have ht (j : Fin 2) : T j = ∑ p : Site c, w j • b j p := invert (T j)
  have hs : D T = ∑ f : Fin 2 → Site c,
      ((∏ j : Fin 2, w j) * D (fun j => b j (f j))) := by
    calc
      D T = D (fun j => ∑ p : Site c, w j • b j p) := congrArg D (funext ht)
      _ = ∑ f : Fin 2 → Site c, D (fun j => w j • b j (f j)) :=
        D.toMultilinearMap.map_sum (fun j p => w j • b j p)
      _ = _ := Finset.sum_congr rfl fun f _ => by
        simpa only [smul_eq_mul] using D.map_smul_univ w (fun j => b j (f j))
  have hprod : (∏ j : Fin 2, w j) = size u/d * (size v/d) := by
    rw [Fin.prod_univ_two]
    rfl
  have hp : 0 ≤ ∏ j : Fin 2, w j :=
    Finset.prod_nonneg fun j _ => div_nonneg (size_nonneg _) hd.le
  have hres (f : Fin 2 → Site c) : |D (fun j => b j (f j))| ≤ E := by
    have he : (fun j => b j (f j)) =
        ![Precision.wave (f 0) (normalized u (f 0)), Precision.wave (f 1) (normalized v (f 1))] := by
      funext j; fin_cases j <;> rfl
    rw [he]
    exact h _ _ _ _ (normalized_bound u _) (normalized_bound v _)
  change |D T| ≤ _
  rw [hs]
  calc
    |∑ f : Fin 2 → Site c, (∏ j : Fin 2, w j) * D (fun j => b j (f j))| ≤
        ∑ f : Fin 2 → Site c, |(∏ j : Fin 2, w j) * D (fun j => b j (f j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _f : Fin 2 → Site c, (∏ j : Fin 2, w j)*E := Finset.sum_le_sum fun f _ => by
      rw [abs_mul, abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_left (hres f) hp
    _ = E*size u*size v := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, hprod]
      push_cast
      change d^2*(size u/d*(size v/d)*E) = _
      field_simp

variable {R : Type} [Fintype R] [DecidableEq R] {A : Census R}
    {P : History G} (Y : Bulk.Chain P) (N m p : ℕ) (hm : m < N)
    (F : Tree.Forest (P.levels.clock.op m p).ratio) (t : (P.levels.clock.op m p).Choices)
    (W : Bulk.Colors A G (P.S.side (m+1) p)) (r : ℕ)

/-- The true, signed native response error, now on arbitrary real mixed
directions. Its coefficient and finite-volume estimate are inherited
without a Fourier-norm loss. -/
theorem actual (hW : W.Standard) (hr : 2 ≤ r)
    (u v : fieldDir G (P.S.side m p) 1) :
    |iteratedFDeriv ℝ 2 (MSFixedRatioSignedReading.quadratic Y N m p hm F t W r) 0 ![u,v] -
      iteratedFDeriv ℝ 2 (draft (Y.kin.alpha N m) (P.rep N p m).path
        (P.rep N p m).clip) 0 ![u,v]| ≤
      ((Fintype.card (Site (P.S.side m p)) : ℝ) * Y.post.Γ (P.levels.clock.J (m+1)) *
        P.levels.clock.loopCap (m+1) *
        Real.exp (-(Y.post.c (P.levels.clock.J (m+1))) * (P.S.side m p).val)) * size u * size v := by
  let D := iteratedFDeriv ℝ 2 (MSFixedRatioSignedReading.quadratic Y N m p hm F t W r) 0 -
    iteratedFDeriv ℝ 2 (draft (Y.kin.alpha N m) (P.rep N p m).path (P.rep N p m).clip) 0
  exact lift D _ (fun i j σ τ hσ hτ =>
    MSFixedRatioSignedReading.wave Y N m p hm F t W r hW hr i j σ τ hσ hτ) u v

end YM.Integration.MSFixedRatioFourierLifting
end
