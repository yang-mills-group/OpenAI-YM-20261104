import YM.WilsonMS.Top.TreeSplit

/-!
# The tree propagator in the based BV calculation

View tree slice as a Lagrangian plane (vanishing tree links, K on
the tree links, c on the based Lie algebra, vanishing c-antifields).
Use the bosonic inverse Hessian of XSpace.Period's slice calculation
itself; prove this is indeed the required inverse for the BV gauge lemma.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Root
open XSpace Period Lattice Function Filter Set Finset
open MS MS.Bare MS.Bare.Focus MS.Cylinder MS.Cylinder.Taylor MS.Native
open MS.Koszul MS.Book MS.Book.Convolve Darboux Matrix
open scoped Topology Matrix.Norms.Frobenius ContDiff

variable {P : Period} (T : P.Tree) (G : Gauge)
local notation "ℐ" => inclusion (freeI T G)

def plantL : T.Field G →L[ℝ] LogSpace G P :=
  (LinearMap.pi (fun e : P.Link => (LinearMap.proj e.val).comp T.covering)).toContinuousLinearMap

lemma plant_apply (u : T.Field G) (e : P.Link) : plantL T G u e = T.prolong u e :=
  T.covering_at u e

lemma plantA_basis (i : T.Key G) :
    plantL T G (T.basis G i) = (coordinates T G).e0 (a (freeI T G i)) := by
  funext x
  rw [plant_apply]
  unfold Tree.prolong
  change dite _ _ _ = Native.priv (freeI T G i) x
  cases i with
  | mk y j =>
    simp only [Pi.basis_apply, Tree.basis, priv, freeI]
    split
    next h =>
      have hk : x ≠ y.val := fun hv => y.property (hv ▸ h)
      rw [Pi.single_eq_of_ne hk]
    next h =>
      by_cases he : x = y.val
      · subst x
        simp
      have hv : (⟨x, h⟩ : T.Free) ≠ y := fun hh => he (congr_arg Subtype.val hh)
      rw [Pi.single_eq_of_ne he, Pi.single_eq_of_ne hv]

lemma plant_exp (x : T.Field G) : raised G (plantL T G x) = T.drape (G.lieExp ∘ x) := by
  funext e
  by_cases he : e ∈ T.edges
  · change G.lieExp _ = T.drape _ _
    rw [plant_apply, Tree.prolong, dif_pos he, G.mat_lieExp_zero]
    exact (T.drape_tree _ ⟨e, he⟩).symm
  change G.lieExp _ = T.drape _ _
  rw [plant_apply, Tree.prolong, dif_neg he]
  exact (T.drape_free (G.lieExp ∘ x) ⟨e, he⟩).symm

lemma relative_action : energyE P G ∘ plantL T G = -T.action (G := G) := by
  ext x
  rw [Function.comp_apply, energyE, plant_exp]
  rfl

lemma ink_same_args {A X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {f g : A → X} (F : X → ℝ)
    (l : List A) (h : ∀ i ∈ l, f i = g i) : ink f F l = ink g F l := by
  induction l generalizing F with
  | nil => rfl
  | cons i l ih =>
    rw [ink, ink, h _ (List.mem_cons_self ..)]
    exact ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj))

def Qslice : Matrix (T.Key G) (T.Key G) ℂ :=
  (T.hessian G).map Complex.ofReal

open Classical in
def treeDirection : Root.Mode T G → T.Field G := fun i =>
  ∑ j : T.Key G, (if a (freeI T G j) = i then (1 : ℝ) else 0) • T.basis G j

lemma tree_direction (i : T.Key G) : treeDirection T G (a (freeI T G i)) = T.basis G i := by
  classical
  unfold treeDirection
  rw [Finset.sum_eq_single_of_mem i (mem_univ _), if_pos rfl, one_smul]
  intro j _ hj
  rw [if_neg, zero_smul]
  exact fun he => hj (free_inj T G (Sum.inl.inj (Sum.inl.inj he)))

lemma precision_restriction : (ℐ)ᵀ * precisionM T G * ℐ = Qslice T G := by
  classical
  let Y := treeDirection T G
  let X := coordinates T G
  let A := plantL T G
  let U := energyE P G
  have h : ink Y (-T.action (G := G)) = ink (A ∘ Y) U :=
    relative_action T G ▸ ink_ctrl_one Y A (energy_germ P G)
  ext i j
  rw [col_inclusion, row_inclusion]
  let x : Root.Mode T G := a (freeI T G i)
  let y : Root.Mode T G := a (freeI T G j)
  have hx (k : T.Key G) : X.e0 (a (freeI T G k)) = (A ∘ Y) (a (freeI T G k)) := by
    dsimp only [Function.comp_apply, Y]
    rw [tree_direction]
    exact (plantA_basis T G _).symm
  change -ink X.e0 U [x, y] = ↑(T.hessian G i j)
  rw [ink_same_args U [x, y]
      (show ∀ i ∈ [x, y], X.e0 i = (A ∘ Y) i from
        by
        intro i hi
        simp at hi
        rcases hi with hi | hi <;> subst i <;> exact hx _),
    ← h]
  let F := T.action (G := G)
  let K := T.hessian G
  have hF : germ F := T.continuousJet G
  rw [← neg_one_smul ℝ F, ink_smul Y hF, Pi.smul_apply, Complex.ofReal_neg, Complex.ofReal_one,
    neg_one_smul, neg_neg]
  change ((layer (Y y) (layer (Y x) F) 0 : ℝ) : ℂ) = (K i j : ℂ)
  have H : layer (Y y) (layer (Y x) F) 0 = iteratedFDeriv ℝ 2 F 0 ![Y y, Y x] := by
    unfold layer
    rw [((hF.fderiv_right (m := ω) (by simp)).differentiableAt (by simp) |>.hasFDerivAt.clm_apply
          (hasFDerivAt_const (Y x) _) |>.fderiv)]
    simp [iteratedFDeriv_two_apply]
  rw [H, show Y x = _ from tree_direction T G i, show Y y = _ from tree_direction T G j,
    show iteratedFDeriv ℝ 2 F 0 _ = K j i from (T.hessian_entries G j i).symm]
  have hT : K j i = K i j := by simpa using (T.hessian_posDef G).1.apply i j
  rw [hT]

def Cslice : Matrix (T.Key G) (T.Key G) ℂ :=
  (T.covariance G).map Complex.ofReal

lemma Cslice_symm : (Cslice T G)ᵀ = Cslice T G := by
  ext i j
  refine congr_arg Complex.ofReal ?_
  simpa using (T.covariance_posDef G).1.apply i j

lemma inverted : Cslice T G * Qslice T G = 1 := by
  have he := T.covariance_val G
  have hh : Qslice T G * Cslice T G = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have ht := congr_arg Complex.ofReal (congr_fun (congr_fun he i) j)
    rw [Matrix.mul_apply] at ht
    push_cast at ht
    change ∑ k : T.Key G, (↑(T.hessian G i k) : ℂ) * ↑(T.covariance G k j) = _
    rw [ht]
    simp only [Matrix.one_apply]
    split <;> simp
  exact mul_eq_one_comm.mp hh

def cutCov : Matrix (LinksI G P) (LinksI G P) ℂ :=
  ℐ * Cslice T G * (ℐ)ᵀ

lemma tree_splitting : Splitting (precisionM T G) (gradientM T G) (cutCov T G) (cutL T G)
    where
  left := cut_left ..
  symmC := by
    rw [cutCov, transpose_mul, transpose_mul, Cslice_symm, transpose_transpose, Matrix.mul_assoc]
  symmH := precision_symm ..
  inverse := by
    refine identifies_R T G ?_ ?_
    · rw [Matrix.add_mul, Matrix.mul_assoc (gradientM T G), cut_free, Matrix.mul_zero, add_zero]
      rw [cutCov, Matrix.mul_assoc (ℐ * Cslice T G), Matrix.mul_assoc (ℐ * Cslice T G),
        precision_restriction, Matrix.mul_assoc, inverted, Matrix.mul_one, Matrix.one_mul]
    rw [Matrix.add_mul, Matrix.mul_assoc (cutCov T G), Matrix.mul_assoc (gradientM T G),
      gradient_kernel, cut_left, Matrix.mul_zero, Matrix.mul_one, zero_add, Matrix.one_mul]
end YM.WilsonMS.Root
