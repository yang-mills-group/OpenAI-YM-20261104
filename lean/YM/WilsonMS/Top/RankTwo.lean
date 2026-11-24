import YM.WilsonMS.Top.BasedAction

/-! # The quadratic kernel of the based BV calculation -/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Root
open XSpace Period Lattice Function Filter Set Finset
open MS MS.Bare MS.Bare.Focus MS.Cylinder MS.Cylinder.Taylor MS.Native
open MS.Koszul MS.Book MS.Book.Convolve Darboux Matrix
open scoped Topology Matrix.Norms.Frobenius ContDiff

variable {P : Period} (T : P.Tree) (G : Gauge)

/-- link precision, from the Wilson action -/
def precisionM : Matrix (LinksI G P) (LinksI G P) ℂ := fun i j =>
  -ink (coordinates T G).e0 (energyE P G) [a i, a j]

/-- columns of exact link jets at the trivial saddle -/
def gradientM : Matrix (LinksI G P) (GhostI T G) ℂ := fun i j =>
  ↑((coordinates T G).seed i (localVector T G j 0))

lemma precision_symm : (precisionM T G)ᵀ = precisionM T G := by
  have h := ink_s _ (coordinates T G |>.never) (energy_germ P G)
  ext i j
  apply congr_arg Neg.neg
  exact (h [] (a j) (a i) []).trans (one_mul _)

private lemma seed_zero (j) :
    launch (coordinates T G) (Native.colorTerm G T.Nonroot) (localVector T G) j [] = 0 :=
  launchFrom T G j [] (by simp)

private def coupled : Raw (Root.Mode T G) ℂ :=
  (pairs T G).hung (launch (coordinates T G) (Native.colorTerm G T.Nonroot) (localVector T G))

private lemma primary (i j : LinksI G P ⊕ GhostI T G) : coupled T G [Sum.inl i, Sum.inl j] = 0 := by
  unfold coupled Bonded.hung
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro y _
  rw [Pi.smul_apply,
    show product (Darboux.parity (E := LinksI G P) (U := GhostI T G)) (atLetter _) _ [_, _] = (0 : ℂ)
      from ?_,
    smul_zero]
  rw [D_eval (Sum.inl i) (product _ _ _), D_product]
  simp only [unheard _ (show Sum.inl i ≠ (pairs T G).dual y from (pairs T G).diff i y), map_zero,
    LinearMap.zero_apply, zero_add]
  rw [(speaks_p _).signs, map_smul, LinearMap.smul_apply, Pi.smul_apply]
  suffices he : product (dg T G) (atLetter ((pairs T G).dual y)) _ [Sum.inl j] = (0 : ℂ) by
    rw [he, smul_zero]
  rw [D_eval _ (product _ _ _), D_product, Pi.add_apply, nil_product, nil_product,
    unheard _ (show Sum.inl j ≠ (pairs T G).dual y from (pairs T G).diff j y), Pi.zero_apply, at_sign]
  simp [atLetter]

private theorem shadow_head (j : GhostI T G) (i : Root.Mode T G) : coupled T G [b j, i] = 0 := by
  let F := chartFocus T G
  let B := pairs T G
  let z := F.KId j
  let Y := coordinates T G
  let L := launch Y (Native.colorTerm G T.Nonroot) (localVector T G)
  change D (B.dual z) (B.hung L) [i] = 0
  have hp : B.Lifted L := lifting _ _ _ (site_lie T G |>.smooth)
  rw [hp.acted, show L z = F.shadow _ _ from launch_shadow .., Pi.smul_apply]
  suffices he : (F.shadow (Native.colorTerm G T.Nonroot) j) [i] = 0 by rw [he, smul_zero]
  unfold shadow
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_
  rw [show product _ (F.spark l) (F.spark k) [i] = 0 from ?_, smul_zero]
  have hx (k) : From (F.spark k) 1 := by
    intro v hv
    cases v
    rfl
    simp at hv
    omega
  exact From.pair (hx l) (hx k) [i] (by simp)

private lemma link_row (i : LinksI G P) (x : Root.Mode T G) :
    coupled T G [k i, x] = Darboux.symbol (precisionM T G) (gradientM T G) (k i) x := by
  classical
  let F := chartFocus T G
  let B := pairs T G
  let z := F.AId i
  let Y := coordinates T G
  let V := Native.colorTerm G T.Nonroot
  let L := localVector T G
  change D (B.dual z) (B.hung (launch Y V L)) [x] = _
  rw [(lifting Y V L (site_lie T G |>.smooth)).acted, show B.fee z = (1 : ℂ) from rfl, one_smul,
    launch_stone]
  unfold stone
  rw [Finset.sum_apply]
  have h j :
    (product (dg T G) (F.spark j) (ink Y.e0 (Y.seed i ∘ L j))) [x] =
      if x = c j then gradientM T G i j else 0 := by
    rw [D_eval _ (product _ _ _), D_product, Pi.add_apply, nil_product, nil_product, at_sign]
    change atLetter (c j) [x] * ink _ _ [] + cross _ _ * 0 * _ = _
    rw [mul_zero, zero_mul, add_zero]
    by_cases hp : x = c j
    · rw [if_pos hp, hp, speaks, one_mul]
      rfl
    rw [if_neg hp, notNamed _ hp, zero_mul]
  change ∑ j : GhostI T G, (product (dg T G) (F.spark j) (ink Y.e0 _)) _ = _
  simp_rw [h]
  rcases x with (x | x) | (x | x) <;> simp [c, Darboux.symbol]

lemma rank2 (i j : Root.Mode T G) :
    free T G [i, j] = Darboux.symbol (precisionM T G) (gradientM T G) i j := by
  let Y := coordinates T G
  rw [free, enough _ (by simp)]
  have hs := uncoupled_symm T G
  have he (d : LinksI G P ⊕ GhostI T G) (i : Root.Mode T G) :
    uncoupled T G [Sum.inr d, i] = coupled T G [Sum.inr d, i] := by
    change ink Y.e0 (energyE P G) _ + _ = _
    rw [D_eval (Sum.inr d) (ink _ _), ink_off _ (show Y.e0 (Sum.inr d) = 0 from Y.dual_off _),
      Pi.zero_apply, zero_add]
    rfl
  have hP (x y : LinksI G P ⊕ GhostI T G) :
    uncoupled T G [Sum.inl x, Sum.inl y] =
      Darboux.symbol (precisionM T G) (gradientM T G) (Sum.inl x) (Sum.inl y) := by
    change ink Y.e0 _ _ + coupled T G _ = _
    rw [primary, add_zero]
    rcases x with i | i
    · rcases y with j | j
      · change _ = - -(ink Y.e0 (energyE P G) [_, _])
        rw [neg_neg]
      have H : Symm (dg T G) (ink Y.e0 (energyE P G)) := ink_s _ Y.never (energy_germ P G)
      refine (H [] (a i) (c j) []).trans ?_
      rw [show ink Y.e0 (energyE P G) ([] ++ [c j, a i]) = 0 from
          congr_fun (ink_off _ (Y.spark_off j) (energyE P G)) [a i],
        mul_zero]
      rfl
    exact congr_fun (ink_off _ (Y.spark_off i) (energyE P G)) [Sum.inl y]
  have HK (x) (j : Root.Mode T G) :
    uncoupled T G [Sum.inr x, j] = Darboux.symbol (precisionM T G) (gradientM T G) (Sum.inr x) j := by
    rw [he]
    rcases x with x | x
    exact link_row T G x j
    exact shadow_head T G x j
  rcases i with i | i
  swap
  · exact HK _ _
  rcases j with j | j
  · exact hP _ _
  refine (hs [] (Sum.inl i) (Sum.inr j) []).trans ?_
  rw [List.nil_append, HK]
  rcases i with i | i <;> rcases j with j | j <;> simp [dg, Darboux.parity, Darboux.symbol]

lemma gradient_kernel : precisionM T G * gradientM T G = 0 := by
  classical
  let H := precisionM T G
  let R := gradientM T G
  let h := free T G
  let m := pairs T G
  have ht := quadratic T G
  have hp := rank2 T G
  ext i j
  change (H * R) i j = 0
  let Z (s : Root.Mode T G) := atLetter s (R := ℂ)
  let V := classicalD m h
  have he : V (V (Z (k i))) = 0 := ht.classical_square (speaks_s _)
  rw [show V (Z (k i)) = ∑ j, (-H i j) • Z (a j) from Darboux.leg_k ht hp i, map_sum] at he
  simp_rw [map_smul,
    show ∀ k : LinksI G P, V (Z (a k)) = ∑ j, R k j • Z (c j) from Darboux.leg_a ht hp] at he
  rw [show (∑ j, (-H i j) • ∑ s, R j s • Z (c s)) = ∑ s, ((-H) * R) i s • Z (c s) from
      mul_line (-H) R i c,
    Matrix.neg_mul] at he
  have hv := congr_fun he [c j]
  rw [Finset.sum_apply, Finset.sum_eq_single_of_mem j (mem_univ _), Pi.smul_apply,
    show Z (c j) [c j] = 1 from speaks _, smul_eq_mul, mul_one] at hv
  · exact neg_eq_zero.mp hv
  intro s _ h
  rw [Pi.smul_apply, show Z (c s) [c j] = 0 from notNamed _ (by simp [c, Ne.symm h]), smul_zero]

lemma gradient_def (i : LinksI G P) (j : GhostI T G) :
    gradientM T G i j = ↑((endsMap T G i.1 (priv j)).2 i.2 - (endsMap T G i.1 (priv j)).1 i.2) := by
  unfold gradientM coordinates
  rw [projector_k, value_local, show (0 : LogSpace G P) i.1 = (0 : G.Color) from rfl,
    Maurer.volt_zero]
  rfl

end YM.WilsonMS.Root
