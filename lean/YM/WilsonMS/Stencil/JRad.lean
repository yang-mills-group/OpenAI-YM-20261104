import YM.WilsonMS.Stencil.PoleSym
/-!
# Pick the common curvature-jet convention

Implement (Jrad) rather than choosing a dimensional continuation based only
on its free specialization. Taylor index i+1 of the connection, i covariant
derivative slots on the curvature. Define these nodes as *D-continued* MS
symbols. To any required grade we then make the physical comparison on a four-
dimensional free-diagnostic basis. Evanescent extensions outside that problem
are not in the theorem.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.JRad
open Function Filter Set Finset MeasureTheory
open MS Plane Koszul Heat Flux Landau Arts Pilot Spin Wire Rock _root_.YM.MS.Shine Outlook
open MvPolynomial Labels Analysis Tensor Maxwell Motif Halo Mach Lifting Theater HBeam Detect
open Complex (I)
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {m n k i j : ℕ} {z : ℂ} {a b c : Axis}
section curvature

variable (G n) in
abbrev direction (z : ℂ) (x : E4) : Module.End ℂ (Mield G n) :=
  ∑ i : Axis, (x i : ℂ) • convoke z (chair n i)

def rayF (z : ℂ) (x : E4) (a b : Axis) (i : ℕ) : Mield G n :=
  (direction G n z x ^ i) (cur z (chair n a) (chair n b))

def volume (i : ℕ) : ℝ :=
  ((i + 2 : ℝ) * (Nat.factorial i : ℝ))⁻¹

def node (z : ℂ) (a : Axis) (i : ℕ) (x : E4) : Mield G n :=
  (volume i) • ∑ j : Axis, (x j : ℝ) • rayF z x j a i

lemma ray_flip (x : E4) : rayF (G := G) (n := n) z x a b i = -rayF z x b a i := by
  have he (a b : Arts.L n) : cur z a b = -cur (G := G) z b a := by
    unfold cur F₀
    rw [jaw_skew ((realA a).tune) ((realA b).tune)]
    simp
    abel
  unfold rayF
  rw [he, map_neg]

lemma zero_form (z : ℂ) (i : ℕ) (x : E4) : (∑ a, x a • node (n := n) (G := G) z a i x) = 0 := by
  apply neg_eq_self.mp
  unfold node
  simp_rw [Finset.smul_sum, ← Finset.sum_neg_distrib, ← smul_neg]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← ray_flip]
  module

lemma ray_sum (x : E4) (i : ℕ) :
    rayF z x a b i = ∑ l : Fin i → Axis, (∏ k : Fin i, x (l k)) • Pole G n a b z (List.ofFn l) := by
  induction i with
  | zero => simp [rayF, Pole]
  | succ i ih =>
    rw [rayF, pow_succ']
    change direction G n z x (rayF z x a b i) = _
    rw [direction, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    let f (l : Fin (i + 1) → Axis) := (∏ k : Fin _, x (l k)) • Pole G n a b z (List.ofFn l)
    have hF : ∑ l : Fin (i + 1) → Axis, f l = ∑ j : Axis, ∑ l : Fin i → Axis, f (Fin.cons j l) := by
      rw [← Equiv.sum_comp (Fin.consEquiv _) f, Fintype.sum_prod_type]
      rfl
    rw [hF]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ih, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold f
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ, Pole]
    rw [mul_smul, LinearMapRealm]
    rfl

lemma line_shape (c : G.ColorIndex) (l : Legs (Shore G n)) (z : ℂ) (a : Axis) (x : ℕ) :
    Plane.Shape (fun i : E4 => node z a x i c l) (x + 1 : ℤ) := by
  simp only [node, ray_sum, Pi.smul_apply, Finset.sum_apply]
  refine ⟨?_, fun v => by omega, fun t i => ?_⟩
  · fun_prop
  simp only [PiLp.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_one (R := ℤ), ← Nat.cast_add, zpow_natCast, pow_succ]
  simp_rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  module

variable (z) in
def beacon (ρ : ℂ →L[ℝ] ℝ) (a : Axis) (i : ℕ) (l : Legs (Shore G n)) : Tensor.T E4 G.Color (i + 1) :=
  ∑ c : G.ColorIndex,
    (ContinuousLinearMap.toSpanSingleton ℝ (cl G c)).compContinuousMultilinearMap
      (ρ.compContinuousMultilinearMap (Tensor.coeff (fun x : E4 => node z a i x c l) (i + 1) 0))

lemma beacon_at (ρ : ℂ →L[ℝ] ℝ) (a : Axis) (l : Legs (Shore G n)) (x : E4) (i : ℕ) :
    Tensor.diagonal (beacon z ρ a i l) x = ∑ c, ρ (node z a i x c l) • cl G c := by
  unfold Tensor.diagonal beacon
  rw [_root_.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  change ρ (Tensor.diagonal _ x) • cl G c = _
  rw [←
    Plane.Shape.form (j := i + 1)
      (by
        convert line_shape c l z a i using 1
        norm_cast)]

lemma beacon_c (ρ : ℂ →L[ℝ] ℝ) (a : Axis) (l : Legs (Shore G n)) (x : E4) (i : ℕ) (c : G.ColorIndex) :
    Tensor.diagonal (beacon z ρ a i l) x c = ρ (node z a i x c l) := by
  rw [beacon_at]
  simp [cl, Pi.single_apply, mul_ite]

lemma beacon_sym (ρ : ℂ →L[ℝ] ℝ) (a : Axis) (l : Legs (Shore G n)) (i : ℕ) :
    Tensor.Sym (beacon z ρ a i l) := by
  intro v s
  unfold beacon
  rw [_root_.sum_apply, _root_.sum_apply]
  exact
    Finset.sum_congr rfl fun j _ =>
      congr_arg (ContinuousLinearMap.toSpanSingleton ℝ (cl G j) ∘ ρ)
        (Tensor.coeff_symm ((line_shape j l z a i).smooth.of_le (by exact_mod_cast le_top)).contDiffAt
          v s)

def antenna (z : ℂ) (ρ : ℂ →L[ℝ] ℝ) (i : ℕ) (l : Legs (Shore G n)) : Labels.Taylor G i :=
  ⟨fun a => beacon z ρ a i l, fun a => beacon_sym _ _ _ _, fun x => by
    ext c
    change ((∑ i' : Axis, x i' • Tensor.diagonal _ _ : G.Color) c) = 0
    let P := ∑ j : Axis, x j • node (G := G) (n := n) z j i x
    have hh : P c l = 0 := by
      rw [show P = _ from zero_form (G := G) (n := n) z i x]
      rfl
    rw [← map_zero ρ, ← hh]
    unfold P
    simp [beacon_c]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← Complex.real_smul]
    exact (map_smul ρ _ _).symm⟩

def factor (G : Gauge) (i : ℕ) : Module.Dual ℝ (Labels.Taylor G i) →ₗ[ℝ] (ℂ → Mob G)
    where
  toFun L z _ l := (L (antenna z Complex.reCLM i l) : ℂ) + I * (L (antenna z Complex.imCLM i l) : ℂ)
  map_add' L K := by
    funext i n l
    simp only [LinearMap.add_apply, Complex.ofReal_add, Pi.add_apply]
    ring
  map_smul' c L := by
    funext z n l
    simp only [LinearMap.smul_apply, smul_eq_mul, Complex.ofReal_mul, Pi.smul_apply,
      Complex.real_smul, RingHom.id_apply]
    ring
variable (G i)

def reading (x : E4) (a : Axis) (c : G.ColorIndex) : Module.Dual ℝ (Labels.Taylor G i) :=
  { toFun V := V.value a x c, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

lemma corresponding (x : E4) (a : Axis) (c : G.ColorIndex) (z : ℂ) (n : ℕ) :
    factor G i (reading G i x a c) z n = node z a i x c := by
  funext l
  change
    ((Tensor.diagonal (beacon z Complex.reCLM a i l) x c : ℝ) : ℂ) +
        I * ((Tensor.diagonal (beacon z Complex.imCLM a i l) x c : ℝ) : ℂ) =
      _
  rw [beacon_c, beacon_c, mul_comm I]
  exact Complex.re_add_im _

lemma enough :
    Submodule.span ℝ {f : Module.Dual ℝ (Labels.Taylor G i) | ∃ x a c, f = reading G i x a c} = ⊤ := by
  let V := Submodule.span ℝ {f : Module.Dual ℝ (Labels.Taylor G i) | ∃ x a c, f = reading G i x a c}
  have hp : V.dualCoannihilator = ⊥ := by
    refine le_antisymm (fun x hx => (Submodule.mem_bot _).mpr ?_) bot_le
    refine Labels.Taylor.value_ext x 0 ?_
    funext j y
    apply WithLp.ofLp_injective 2
    funext c
    exact
      (Submodule.mem_dualCoannihilator x).mp hx (reading G i y j c)
        (Submodule.subset_span (Set.mem_setOf.mpr ⟨y, j, c, rfl⟩))
  apply Submodule.eq_top_of_finrank_eq
  rw [Subspace.dual_finrank_eq]
  have he := Subspace.finrank_add_finrank_dualCoannihilator_eq V
  rw [hp] at he
  simpa using he
end curvature
end YM.WilsonMS.JRad
