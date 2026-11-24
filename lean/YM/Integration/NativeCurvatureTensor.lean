import YM.Comparison.Density.RenderM.Inflect
import YM.PertExtension.HueMean
import YM.Next.RANK.Common

/-!
Exact finite tensorization of gauge-invariant curvature polynomials. Haar
averaging acts on the original color tensors and retains every monomial,
including the constant term. The Token constructor retains the supplied
paths, support, test amplitude and complex coefficient cost. No packet-width,
mask compensation, full-Q remainder or normalized integral estimate is
asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativeCurvatureTensor

open Function Finset MeasureTheory MvPolynomial Lattice Wilson RG
open PertExtension Next.Rank
open Comparison.Density Comparison.Density.RenderM
open Comparison.Density.Testing Markers Marker
open scoped BigOperators Classical Topology
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {t : ℕ}

/-- The literal invariant color tensor of one ordered coordinate monomial. -/
def coefficient (c j : Fin t → G.ColorIndex) : ℂ :=
  ∫ g : G.El, ∏ i, (G.adjoint g (EuclideanSpace.basisFun _ ℝ (j i)) (c i) : ℂ)
    ∂G.probHaar

def value (c : Fin t → G.ColorIndex) (v : Fin t → G.Color) : ℂ :=
  ∑ j : Fin t → G.ColorIndex, (↑(∏ i, v i (j i)) : ℂ) * coefficient c j

private theorem coordinate (g : G.El) (v : G.Color) (k : G.ColorIndex) :
    (G.adjoint g v k : ℂ) =
      ∑ j, (v j : ℂ) * (G.adjoint g (EuclideanSpace.basisFun _ ℝ j) k : ℂ) := by
  let B := (EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis
  have he : v = ∑ j, B.repr v j • B j := (B.sum_repr v).symm
  have hv j : B.repr v j = v j := by dsimp only [B]; simp
  conv_lhs => rw [he, _root_.map_sum]
  simp_rw [map_smul]
  rw [show ∀ f : G.ColorIndex → G.Color,
    (∑ i, f i).ofLp k = ∑ j, (f j).ofLp k from
      fun f => map_sum (EuclideanSpace.proj k : G.Color →L[ℝ] ℝ) f _,
    Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hv]
  change ((v j * G.adjoint g (B j) k : ℝ) : ℂ) = _
  rw [Complex.ofReal_mul]
  rfl

@[fun_prop] private theorem coordinate_continuous (v : G.Color) (k : G.ColorIndex) :
    Continuous (fun g : G.El => (G.adjoint g v k : ℂ)) := by
  have he : (fun g : G.El => (G.adjoint g v k : ℂ)) =
      fun g => ∑ j, (v j : ℂ) *
        (G.adjoint g (EuclideanSpace.basisFun _ ℝ j) k : ℂ) :=
    funext fun g => coordinate g v k
  rw [he]
  fun_prop

private theorem product_integrable (c : Fin t → G.ColorIndex)
    (v : Fin t → G.Color) :
    Integrable (fun g : G.El => ∏ i, (G.adjoint g (v i) (c i) : ℂ))
      G.probHaar := by
  apply Continuous.integrable_of_hasCompactSupport
  · fun_prop
  · exact HasCompactSupport.of_compactSpace _

theorem value_average (c : Fin t → G.ColorIndex) (v : Fin t → G.Color) :
    value c v = ∫ g : G.El, ∏ i, (G.adjoint g (v i) (c i) : ℂ) ∂G.probHaar := by
  unfold value coefficient
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum Finset.univ (fun j _ => ?_)]
  · apply integral_congr_ae
    filter_upwards [] with g
    calc
      _ = ∑ j : Fin t → G.ColorIndex, ∏ i,
          (v i (j i) : ℂ) *
            (G.adjoint g (EuclideanSpace.basisFun _ ℝ (j i)) (c i) : ℂ) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.prod_mul_distrib, Complex.ofReal_prod]
      _ = ∏ i, ∑ j, (v i j : ℂ) *
          (G.adjoint g (EuclideanSpace.basisFun _ ℝ j) (c i) : ℂ) :=
        (Fintype.prod_sum (fun (i : Fin t) (j : G.ColorIndex) =>
          (v i j : ℂ) *
            (G.adjoint g (EuclideanSpace.basisFun _ ℝ j) (c i) : ℂ))).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        exact (coordinate g (v i) (c i)).symm
  · apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact HasCompactSupport.of_compactSpace _

theorem value_invariant (c : Fin t → G.ColorIndex) (v : Fin t → G.Color)
    (u : G.El) :
    value c (fun i => G.adjoint u (v i)) = value c v := by
  rw [value_average, value_average]
  let f (g : G.El) : ℂ := ∏ i, (G.adjoint g (v i) (c i) : ℂ)
  have h (g : G.El) :
      (∏ i, (G.adjoint g (G.adjoint u (v i)) (c i) : ℂ)) = f (g * u) := by
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun w : G.Color => (w (c i) : ℂ)) (G.adjoint_mul g u (v i)).symm
  simp_rw [h]
  exact (measurePreserving_mul_right G.probHaar u).integral_comp
    (Homeomorph.mulRight u).measurableEmbedding f

section Tokens

variable {V : Type} [DecidableEq V] {X : V → Type}
variable [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)]
variable {n : Side}

def token (c : Fin t → G.ColorIndex) (o : Site n) (q : Fin t → RG.Slot)
    (S : Support n) (a : Cross X → ℂ) (C : ℝ) : Token G n X t where
  root := o
  path := q
  gem j x := coefficient c j * a x
  fall := (⟨q, fun _ => 0⟩ : Atom G t).length
  plot := S
  coin := (∑ j : Fin t → G.ColorIndex, ‖coefficient c j‖) * C

omit [DecidableEq V] [∀ v, NormedSpace ℂ (X v)] [∀ v, NormedAddCommGroup (X v)] in
theorem token_touch (c : Fin t → G.ColorIndex) (o : Site n) (q : Fin t → RG.Slot)
    (S : Support n) (a : Cross X → ℂ) (C : ℝ) (x : Cross X)
    (v : Fin t → G.Color) :
    (token c o q S a C).touch x v = value c v * a x := by
  simp only [token, Token.touch, value, Finset.sum_mul, mul_assoc]

omit [DecidableEq V] [∀ v, NormedSpace ℂ (X v)] [∀ v, NormedAddCommGroup (X v)] in
theorem token_read (c : Fin t → G.ColorIndex) (o : Site n) (q : Fin t → RG.Slot)
    (S : Support n) (a : Cross X → ℂ) (C : ℝ) (x : Cross X) (U : Config G n) :
    (token c o q S a C).read x U =
      value c (fun i => (q i).atSite U o) * a x := by
  exact token_touch c o q S a C x _

omit [DecidableEq V] [∀ v, NormedSpace ℂ (X v)] [∀ v, NormedAddCommGroup (X v)] in
theorem token_price (c : Fin t → G.ColorIndex) (o : Site n) (q : Fin t → RG.Slot)
    (S : Support n) (a : Cross X → ℂ) (C : ℝ) (x : Cross X) (hx : ‖a x‖ ≤ C) :
    (∑ j, ‖(token c o q S a C).gem j x‖) ≤ (token c o q S a C).coin := by
  change (∑ j, ‖coefficient c j * a x‖) ≤ (∑ j, ‖coefficient c j‖) * C
  simp_rw [norm_mul]
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_left hx (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem token_alive {R : Census V} (O : Readers V X n) (i : Multi.Hot R)
    (c : Fin t → G.ColorIndex) (o : Site n) (q : Fin t → RG.Slot)
    (S : Support n) (a : Cross X → ℂ) (C : ℝ)
    (hpath : (⟨q, fun _ => 0⟩ : Atom G t).footprint o ⊆ S)
    (hread : Reads O.locus S i.sites a) (hslot : Slotted i.sites a)
    (hincludes : ∀ v, v ∈ i.sites → O.source.uses v ⊆ S)
    (hcost : ∀ x, UnitPage x → ‖a x‖ ≤ C) :
    (token c o q S a C).Alive O i := by
  refine ⟨fun _ => le_refl _, fun _ => hpath, ?_, ?_, ?_, hincludes, ?_⟩
  · intro x v g
    rw [token_touch, token_touch, value_invariant]
  · intro j x y h
    exact congrArg (fun z : ℂ => coefficient c j * z) (hread x y h)
  · intro j
    exact hslot.scale (coefficient c j)
  · intro x hx
    exact token_price c o q S a C x (hcost x hx)

end Tokens

private theorem monomial_word {A : Type*} (m : A →₀ ℕ) :
    ∃ w : Fin (m.sum fun _ k => k) → A,
      (monomial m 1 : MvPolynomial A ℂ) = Normal.glyphs w univ ∧
      ∀ i, w i ∈ m.support := by
  let n := m.sum fun _ k => k
  let U := (k : m.support) × Fin (m k.val)
  have hh : Fintype.card U = n := by
    dsimp only [n, Finsupp.sum]
    simp only [U, Fintype.card_sigma, Fintype.card_fin]
    exact Finset.sum_attach ..
  let e := Fintype.equivFinOfCardEq hh
  let H (z : U) := X (R := ℂ) z.1.val
  let w := fun k : Fin n => (e.symm k).1.val
  refine ⟨w, ?_, fun k => (e.symm k).1.property⟩
  have he : (∏ z : U, H z) = Normal.glyphs w univ :=
    Fintype.prod_equiv e H _ (fun j => by simp only [w, Equiv.symm_apply_apply, H])
  rw [← he, Fintype.prod_sigma H, monomial_eq, map_one, one_mul, Finsupp.prod]
  simp only [H, prod_const, card_univ, Fintype.card_fin]
  exact (Finset.prod_attach m.support (fun k => X k ^ m k)).symm

def word {A : Type*} (m : A →₀ ℕ) : Fin (m.sum fun _ k => k) → A :=
  (monomial_word m).choose

theorem word_mem {A : Type*} (m : A →₀ ℕ) (i : Fin (m.sum fun _ k => k)) :
    word m i ∈ m.support :=
  (monomial_word m).choose_spec.2 i

private theorem word_eq {A : Type*} (m : A →₀ ℕ) :
    (monomial m 1 : MvPolynomial A ℂ) = Normal.glyphs (word m) univ :=
  (monomial_word m).choose_spec.1

/-- All monomials of the original invariant polynomial, with their original
complex coefficients. Every path index lies in that monomial's support. -/
theorem polynomial_value {A : Type*} (p : Hue.Poly A G) (hp : Hue.Fixed p)
    (u : Hue.Mask A G) :
    Hue.display u p =
      ∑ m ∈ p.support, coeff m p *
        value (fun i => (word m i).2) (fun i => u (word m i).1) := by
  have he (g : G.El) :
      Hue.display (Hue.tint g u) p =
        ∑ m ∈ p.support, coeff m p *
          ∏ i, (G.adjoint g (u (word m i).1) (word m i).2 : ℂ) := by
    nth_rw 1 [MvPolynomial.as_sum p]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m _
    have hm : monomial m (coeff m p) = coeff m p • Normal.glyphs (word m) univ := by
      rw [← word_eq, ← map_smul, smul_eq_mul, mul_one]
    rw [hm, map_smul, smul_eq_mul]
    simp only [Hue.display, Hue.tint, Normal.glyphs, map_prod, aeval_X]
  have hav : (∫ g : G.El, Hue.display (Hue.tint g u) p ∂G.probHaar) =
      Hue.display u p := by
    calc
      _ = ∫ _g : G.El, Hue.display u p ∂G.probHaar :=
        integral_congr_ae (Filter.Eventually.of_forall fun g => hp g u)
      _ = _ := by simp
  rw [← hav]
  simp_rw [he]
  rw [integral_finsetSum _ (fun m _ =>
    (product_integrable (fun i => (word m i).2) (fun i => u (word m i).1)).const_mul _)]
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_const_mul, value_average]

end YM.Integration.NativeCurvatureTensor
