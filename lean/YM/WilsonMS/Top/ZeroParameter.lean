import YM.WilsonMS.Top.ColorKernel
import YM.UVNext.FREE_STRESS_CERTIFICATE.Color

/-!
# Exact change to the mean-zero Landau ghost

Only in the Wick computation. This does *not* assume that the constants form
an ideal. On ghost terms of the action it uses global adjoint covariance
on the Landau integration slice. Must precede application of the marked-body
comparison (this is not a proof that general canonical changes **with**
source terms leave `PhysicalSum` unaltered on the finite quotient!).
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Quo
open Function Filter Set Finset Matrix Complex Lattice XSpace
open MS MS.Orbit MS.Bare MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.Native Root Position Darboux
open MS.Orbit.Cog MS.Swirl
open scoped Topology ContDiff Matrix.Norms.Frobenius

private lemma constant_gauge {G : Gauge} (x : G.Color) : Maurer.volts (x, x) =ᶠ[𝓝 0] (G.ad (-x)) := by
  obtain ⟨r, hr, h⟩ := LocalH.geom_patch G
  let H := h r (le_refl r)
  filter_upwards [Metric.ball_mem_nhds (0 : G.Color) hr] with y hy
  let z (t : ℝ) := G.adjoint (G.lieExp (t • (-x))) y
  have hv t : Maurer.step (x, x) y t = G.lieExp (z t) := by
    dsimp only [Maurer.step, z]
    rw [Maurer.runby, smul_neg, Next.SectorChange.exp_negative, inv_inv]
  have hz : ∀ t, z t ∈ Metric.ball 0 r := by
    intro t
    simpa [z] using hy
  have he : Maurer.volts (x, x) y = G.ad (-x) y :=
    (Maurer.amp (x, x) H hy |>.congr_of_eventuallyEq (f₁ := z)
          (Eventually.of_forall fun t => by
            dsimp only
            rw [hv]
            exact (Maurer.snap_on H (hz t)).symm)).unique
      (UVNext.FreeStress.adjoint_derivative (-x) _)
  exact he

variable {P : Period} (T : P.Tree) (G : Gauge)
local notation "Nm'" => LinksI G P
local notation "Qm'" => GhostI T G
local notation "n" => P.side
local notation "J'" => liftJ P G
local notation "M'" => Root.Mode T G
local notation "U'" => SiteField G P.side
local notation "G0" => FFT.originP G.ColorIndex P.side
local notation "T₁" => LogSpace G P
local notation "R0" => coordinates T G
local notation "Y'" => expander P G
local notation "Ro" => Root.localVector T G
local notation "Lp" => landL T G

def actR (P : Period) (G : Gauge) (x : G.Color) : LogSpace G P →L[ℝ] LogSpace G P :=
  (LinearMap.pi fun i : P.Link => (G.ad (-x)).comp (LinearMap.proj i)).toContinuousLinearMap

lemma constant_travel (x : G.Color) : travel G (P := P) (fun _ => x) =ᶠ[𝓝 0] Y' ∘ actR P G x := by
  filter_upwards [eventually_all.mpr
      (fun i : P.Bonds =>
        ((continuous_apply i).comp (Y').continuous |>.tendsto (0 : T₁)).eventually
          (by
            rw [Function.comp_apply, map_zero, Pi.zero_apply]
            exact constant_gauge x))] with
    a ha
  funext i
  change Maurer.volts (x, x) (Y' a i) = _
  rw [show Maurer.volts (x, x) (Y' a i) = _ from ha i]
  change G.ad (-x) (P.extend a i) = P.extend _ i
  unfold Period.extend
  split
  next h => rfl
  next h =>
    rw [map_neg]
    rfl

lemma parameter_move (u : Qm') :
    ∃ w : G.Color, parameter T G (averageM T G) u = parameter T G (liftN T G) u + fun _ => w := by
  let X := -parameter T G (G0 * liftN T G) u
  let Q := G0 * liftN T G
  have hy (x : P.Sites) (c : G.ColorIndex) : X x c = -(Q (c, x) u).re := by
    unfold X parameter
    rw [Pi.neg_apply, PiLp.neg_apply, Finset.sum_apply]
    apply congr_arg Neg.neg
    change
      ((baseC.toBasis).coord c)
          (∑ j : GaugeField G P.side, (_ : ℝ) • (priv (siteEquiv G P.side j) x)) =
        _
    simp_rw [map_sum, map_smul]
    rw [Finset.sum_eq_single_of_mem (c, x) (mem_univ _)]
    · simp [siteEquiv, priv, baseC]
      rfl
    rintro ⟨i, a⟩ _ ha
    by_cases ht : x = a
    · subst a
      have hX : c ≠ i := fun h => ha (Prod.ext h.symm rfl)
      simp [siteEquiv, priv, baseC, hX]
    simp [siteEquiv, priv, ht]
  have hi (a b : P.Sites) : X a = X b := by
    ext i
    rw [hy, hy]
    unfold Q
    rw [arithmeticMean, arithmeticMean]
  refine ⟨X 0, ?_⟩
  rw [← funext (show ∀ i, X i = X 0 from fun i => hi i 0)]
  unfold averageM
  rw [Matrix.sub_mul, Matrix.one_mul]
  unfold X parameter
  simp_rw [Matrix.sub_apply, Complex.sub_re, sub_smul, Finset.sum_sub_distrib, sub_eq_add_neg]

lemma adjusted (u : Qm') (x : G.Color)
    (hx : parameter T G (averageM T G) u = parameter T G (liftN T G) u + fun _ => x) (j : Nm') :
    history T G (parameter T G (averageM T G) u) j =
      history T G (parameter T G (liftN T G) u) j +
        (2 : ℂ) • ink (R0).e0 ((R0).seed j ∘ actR P G x) := by
  let f : T₁ → T₁ := Ro u
  let g := actR P G x
  let v := parameter T G (averageM T G) u
  let w := parameter T G (liftN T G) u
  have he : v = w + (fun _ => x) := hx
  have hv : travel G v =ᶠ[𝓝 0] Y' ∘ (f + ⇑g) := by
    filter_upwards [vBased T G u, constant_travel (P := P) G x] with i ha hb
    change Chart.roam _ _ v = Y' (f i + g i)
    rw [he, map_add, map_add]
    exact congr_arg₂ (· + ·) ha hb
  have hs := (site_lie T G).smooth u
  rw [rooted_history T G _ (_ + ⇑g) (hs.add (g.contDiff.contDiffAt)) hv,
    rooted_history T G _ _ hs (vBased T G u),
    show (R0).seed j ∘ (f + ⇑g) = (R0).seed j ∘ f + (R0).seed j ∘ g from
      funext fun t => map_add ((R0).seed j) _ _,
    ink_add _ ((R0).seed j |>.contDiff.contDiffAt.comp 0 hs)
      ((R0).seed j |>.contDiff.contDiffAt.comp 0 g.contDiff.contDiffAt),
    smul_add]

variable (r : G.Color)
local notation "VAp" => waveQ T G
local notation "Kp" => antiK T G
local notation "vρ" => actR P G r

def byColor {I : Type} [DecidableEq I] (r : G.Color) :
    Matrix (I × G.ColorIndex) (I × G.ColorIndex) ℂ := fun i j =>
  if i.1 = j.1 then ↑((G.ad (-r)) (baseC j.2) i.2) else 0
local notation "Ξ'" => byColor (I := P.Link) G r

lemma color_matrix (i j : Nm') : (↑((R0).seed i ((actR P G r) (priv j))) : ℂ) = Ξ' i j := by
  rw [coordinates, Native.projector_k]
  change (↑(G.ad (-r) (priv j i.1) i.2) : ℂ) = _
  unfold byColor
  split
  next h => rw [priv, h, Pi.single_eq_same]
  next h =>
    rw [priv, Pi.single_eq_of_ne h, map_zero]
    rfl

lemma comm_L : Lp * Ξ' = byColor (I := T.Nonroot) G r * Lp := by
  ext ⟨v, s⟩ ⟨x, i⟩
  simp_rw [Matrix.mul_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type (α₁ := T.Nonroot)]
  simp_rw [tints]
  simp [byColor, mul_ite, ite_mul]
  ring

private lemma rank_one (i : Nm') :
    ink (coordinates T G).e0 ((R0).seed i ∘ vρ) = ∑ j : Nm', Ξ' i j • atLetter (a j) := by
  let f := ((R0).seed i).comp (actR P G r)
  have he y : D y (ink (coordinates T G).e0 ⇑f) = coin (↑(f ((R0).e0 y)) : ℂ) := by
    rw [inktip,
      show layer ((R0).e0 y) ⇑f = (fun _ => f ((R0).e0 y)) from funext fun _ => by simp [layer],
      ink_const]
  have hq : Book.rank 1 (ink (coordinates T G).e0 ⇑f) := by
    intro l h
    rw [Book.mod_int] at h
    cases l with
    | nil => simp
    | cons i l =>
      cases l with
      | nil => simp at h
      | cons j l =>
        rw [D_eval i (ink _ _), he]
        rfl
  change ink (coordinates T G).e0 ⇑f = _
  rw [one_leg _ hq]
  simp_rw [D_eval _ (ink (coordinates T G).e0 ⇑f), he, coin]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type (α₁ := Nm')]
  have ht (j) : (↑(f ((R0).e0 (Sum.inl (Sum.inl j)))) : ℂ) = byColor (I := P.Link) G r i j :=
    color_matrix T G r i j
  simp_rw [ht, show ∀ x, (R0).e0 (Sum.inl (Sum.inr x)) = 0 from fun _ => rfl,
    show ∀ x, (R0).e0 (Sum.inr x) = 0 from fun _ => rfl, map_zero f, Complex.ofReal_zero, zero_smul,
    Finset.sum_const_zero]
  simp only [add_zero]

local notation "πl" => specialize (toLand T G)

lemma projected_c (i : Qm') : πl (atLetter (c i)) = atLetter (c i) := by
  rw [specialize_letter]
  simp [toLand, c, legs, Fintype.sum_sum_type, Letters, Matrix.one_apply]

lemma projected_k (i : Nm') : πl (atLetter (k i)) = ∑ j : Nm', Kp i j • atLetter (k j) := by
  rw [specialize_letter]
  simp [toLand, k, legs, Fintype.sum_sum_type, Letters]

lemma projected_a (i : Nm') : πl (atLetter (a i)) = ∑ j : Nm', VAp i j • atLetter (a j) := by
  rw [specialize_letter]
  simp [toLand, a, legs, Fintype.sum_sum_type, Letters]

lemma linear_r (i : Nm') :
    πl (ink (coordinates T G).e0 ((R0).seed i ∘ vρ)) = ∑ j : Nm', (Ξ' * VAp) i j • atLetter (a j) := by
  rw [rank_one, map_sum]
  simp_rw [map_smul, projected_a]
  exact mul_line Ξ' VAp i a

lemma shutoff : Kpᵀ * (Ξ' * VAp) = 0 := by
  let L := Lp
  let R := gradientM T G
  rw [antiK, transpose_transpose]
  change R * L * _ = 0
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc L, show L * Ξ' = _ from comm_L T G r,
    Matrix.mul_assoc (byColor (I := T.Nonroot) G r), waveQ, Matrix.mul_sub, Matrix.mul_one, ←
    Matrix.mul_assoc Lp R, (Quo.split T G).left, Matrix.one_mul, sub_self]
  simp

lemma passes (u : Qm') :
    πl
        (∑ i : Nm',
          product (dg T G) (atLetter (k i))
            (product (dg T G) (atLetter (c u))
              ((2 : ℂ) • ink (coordinates T G).e0 ((R0).seed i ∘ vρ)))) =
      0 := by
  let A := πl
  let p := dg T G
  have ht (F H : Raw M' ℂ) : A (product p F H) = product p (A F) (A H) :=
    (specialize_tether (plane_wire T G)).craft ..
  let B := product (dg T G) (atLetter (c u) (R := ℂ))
  let F (z j : Nm') := product p (atLetter (k z)) (B ((2 : ℂ) • atLetter (a j)))
  let T' := Ξ' * VAp
  rw [map_sum]
  simp_rw [show ∀ f g : Raw M' ℂ, πl (product (dg T G) f g) = product (dg T G) (πl f) (πl g) from ht,
    projected_c, projected_k, map_smul, linear_r]
  have he i :
    (2 : ℂ) •
        product (dg T G) (∑ z : Nm', Kp i z • atLetter (k z))
          (product (dg T G) (atLetter (c u)) (∑ j : Nm', T' i j • atLetter (a j))) =
      ∑ z : Nm', ∑ j : Nm', (Kp i z * T' i j) • F z j := by
    simp only [Finset.smul_sum, map_sum, map_smul, mul_smul, F, p, B, LinearMap.sum_apply,
      LinearMap.smul_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    module
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => he i)]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Finset.sum_smul,
    show (∑ x : Nm', Kp x j * T' x i) = 0 from
      ((show _ = (Kpᵀ * T') j i from Matrix.mul_apply.symm).trans
        (congr_fun (congr_fun (shutoff T G r) j) i)),
    zero_smul]

/-- Ghost response with `averageM` agrees with the one with `liftN` on the
Landau plane (sufficient because the Wick test factors through this plane).
The difference of parameters is a global rotation, whose contribution is killed
by the A/K supports there (`shutoff`). -/
lemma transmitted :
    specialize (toLand T G) (specialize (location T G (averageM T G)) (wing P G)) =
      specialize (toLand T G) (specialize (location T G (liftN T G)) (wing P G)) := by
  rw [bill_total T G _ (real_average T G), bill_total T G _ (real_based T G)]
  choose r hx using parameter_move T G
  let U := liftN T G
  let V := averageM T G
  let c0 := parameter T G U
  let v := parameter T G V
  let f (j : Qm') (i : Nm') :=
    product (dg T G) (atLetter (k i))
      (product (dg T G) (atLetter (c j))
        ((2 : ℂ) • ink (coordinates T G).e0 ((R0).seed i ∘ actR P G (r j))))
  have he : connected T G v = connected T G c0 + ∑ j, ∑ i, f j i := by
    rw [Finset.sum_comm (f := fun j i => f j i)]
    unfold connected
    simp only [v, c0, V, U, map_sum,
      show ∀ i j, history T G (parameter T G (averageM T G) i) j = _ from fun i j =>
          adjusted T G i (r i) (hx i) j,
      map_add, Finset.sum_add_distrib]
    rfl
  rw [he, map_add, map_sum, Finset.sum_eq_zero, add_zero]
  exact fun i _ => passes T G _ i
end YM.WilsonMS.Quo
