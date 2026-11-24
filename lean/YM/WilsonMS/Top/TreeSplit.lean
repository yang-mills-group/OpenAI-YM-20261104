import YM.WilsonMS.Top.RankTwo

/-! # Decompositions of the log/ghost tangent spaces at tree gauge -/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Root
open XSpace Period Lattice Function Filter Set Finset
open MS MS.Bare MS.Bare.Focus MS.Cylinder MS.Cylinder.Taylor MS.Native
open MS.Koszul MS.Book MS.Book.Convolve Darboux Matrix
open scoped Topology Matrix.Norms.Frobenius ContDiff

section matrix
variable {I J K : Type}

def inclusion [DecidableEq I] (f : J → I) : Matrix I J ℂ := fun i j => if f j = i then 1 else 0

lemma inclusion_at [DecidableEq I] (f : J → I) (j) : inclusion f (f j) j = 1 :=
  if_pos rfl

lemma inclusion_else [DecidableEq I] (f : J → I) (i) (j) (hj : f j ≠ i) : inclusion f i j = 0 :=
  if_neg hj

lemma row_inclusion [Fintype I] [DecidableEq I] (f : J → I) (A : Matrix I K ℂ) (i j) :
    ((inclusion f)ᵀ * A) i j = A (f i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem (f i) (mem_univ _), transpose_apply, inclusion_at,
    one_mul]
  intro k _ hk
  rw [transpose_apply, inclusion_else _ _ _ (Ne.symm hk), zero_mul]

lemma col_inclusion [Fintype I] [DecidableEq I] (f : J → I) (A : Matrix K I ℂ) (i j) :
    (A * inclusion f) i j = A i (f j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem (f j) (mem_univ _), inclusion_at, mul_one]
  intro k _ hk
  rw [inclusion_else _ _ _ (Ne.symm hk), mul_zero]

lemma inclusion_mul [Fintype I] [DecidableEq I] [DecidableEq J] {f : J → I} (hf : Injective f) :
    (inclusion f)ᵀ * inclusion f = 1 := by
  ext i j
  rw [row_inclusion]
  by_cases he : i = j
  rw [he, inclusion_at, Matrix.one_apply_eq]
  rw [Matrix.one_apply_ne he]
  exact inclusion_else _ _ _ (hf.ne (Ne.symm he))

lemma inclusion_cross [Fintype I] [DecidableEq I] {f : J → I} {g : K → I} (h : ∀ j k, f j ≠ g k) :
    (inclusion f)ᵀ * inclusion g = 0 := by
  ext i j
  rw [row_inclusion, inclusion_else _ _ _ (Ne.symm (h i j))]
  rfl

lemma split_apply [Fintype I] [DecidableEq I] (v : I → ℂ) (f : J → I) (i : J) :
    ((inclusion f)ᵀ *ᵥ v) i = v (f i) := by
  change ∑ j : I, inclusion f j i * v j = v _
  rw [Finset.sum_eq_single_of_mem (f i) (mem_univ _), inclusion_at, one_mul]
  intro k _ hk
  rw [inclusion_else _ _ _ (Ne.symm hk), zero_mul]
end matrix

variable {P : Period} (T : P.Tree) (G : Gauge)

def freeI (x : T.Key G) : LinksI G P :=
  (x.1.val, x.2)

lemma free_inj : Injective (freeI T G) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ h
  unfold freeI at h
  simp only [Prod.mk.injEq, Subtype.val_inj] at h
  rw [h.1, h.2]

def treeI (x : GhostI T G) : LinksI G P :=
  (T.edge x.1.val x.1.property, x.2)

lemma tree_inj : Injective (treeI T G) := by
  intro a b h
  refine
    Prod.ext (T.edge_unique (congr_arg Prod.fst h))
      (show (treeI T G a).2 = (treeI T G b).2 from congr_arg Prod.snd h)

lemma disjoint (x : T.Key G) (y : GhostI T G) : freeI T G x ≠ treeI T G y := by
  intro h
  apply x.1.property
  exact (T.mem_edges _).mpr ⟨y.1.val, y.1.property, (congr_arg Prod.fst h).symm⟩

lemma present (x : LinksI G P) : x ∈ Set.range (freeI T G) ∨ x ∈ Set.range (treeI T G) := by
  by_cases h : x.1 ∈ T.edges
  swap
  exact .inl ⟨⟨⟨x.1, h⟩, x.2⟩, rfl⟩
  obtain ⟨a, b, h⟩ := (T.mem_edges _).mp h
  exact .inr ⟨(⟨a, b⟩, x.2), Prod.ext h rfl⟩

local notation "ℐ" => inclusion (freeI T G)
local notation "τ" => inclusion (treeI T G)

def extendedParameter (p : GhostI T G → ℂ) (x : P.Vertex) (i : G.ColorIndex) : ℂ :=
  if h : x ≠ T.root then p (⟨x, h⟩, i) else 0

lemma eval_parameter (p : GhostI T G → ℂ) (x : P.Vertex) (i : G.ColorIndex) :
    ∑ j : GhostI T G, ↑(based T G (priv j) x i) * p j = extendedParameter T G p x i := by
  classical
  by_cases he : x ≠ T.root
  swap
  · simp [based, he, extendedParameter]
    simp_all
  unfold extendedParameter
  rw [dif_pos he, Finset.sum_eq_single_of_mem ((⟨x, he⟩ : T.Nonroot), i) (mem_univ _)]
  · simp [based, he, priv, baseC]
  rintro ⟨j, s⟩ _ hv
  suffices hz : based T G (priv (j, s)) x i = 0 by
    rw [hz]
    simp
  let y : T.Nonroot := ⟨x, he⟩
  by_cases hh : j = y
  · subst j
    have hj : s ≠ i := by
      intro hk
      apply hv
      rw [hk]
    simp [based, he, priv, y, baseC, hj.symm]
  rw [show based T G (priv (j, s)) x = Native.priv (j, s) y from dif_pos he, priv,
    Pi.single_eq_of_ne (Ne.symm hh)]
  rfl

lemma gradient_vector (v) (i : LinksI G P) :
    (gradientM T G *ᵥ v) i =
      extendedParameter T G v (P.dst i.1) i.2 - extendedParameter T G v (P.src i.1) i.2 := by
  rw [← eval_parameter, ← eval_parameter, ← Finset.sum_sub_distrib]
  unfold mulVec dotProduct
  refine Finset.sum_congr rfl (fun j _ => ?_)
  change gradientM T G i j * v j = _
  rw [gradient_def]
  push_cast
  rw [sub_mul]
  rfl

def treeMatrix : Matrix (GhostI T G) (GhostI T G) ℂ :=
  (τ)ᵀ * gradientM T G

lemma treeInject : Injective (fun v => (treeMatrix T G) *ᵥ v) := by
  have hz (v : GhostI T G → ℂ) (h : (treeMatrix T G) *ᵥ v = 0) : v = 0 := by
    unfold treeMatrix at h
    rw [← mulVec_mulVec] at h
    let W := extendedParameter T G v
    have hh (x : T.Nonroot) (j : G.ColorIndex) : W x j = W (T.parent x) j := by
      have ht := congr_fun h (x, j)
      rw [split_apply, gradient_vector] at ht
      change W (P.dst (T.edge x.val x.property)) j - W (P.src (T.edge x.val x.property)) j = 0 at ht
      rcases T.joins _ x.property with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b] at ht
      · exact (sub_eq_zero.mp ht).symm
      exact sub_eq_zero.mp ht
    have hp (x : P.Vertex) (j : G.ColorIndex) : W x j = 0 := by
      induction he : T.rank x using Nat.strong_induction_on generalizing x with
      | h n ih =>
        by_cases hx : x = T.root
        · simp [W, hx, extendedParameter]
        rw [show W x j = _ from hh ⟨x, hx⟩ j]
        exact ih _ (he ▸ T.closer x hx) _ rfl
    funext j
    obtain hw := hp j.1 j.2
    unfold W extendedParameter at hw
    rw [dif_pos j.1.property] at hw
    exact hw
  intro v w he
  dsimp only at he
  apply sub_eq_zero.mp
  refine hz _ ?_
  rw [mulVec_sub, he, sub_self]

lemma tree_unit : IsUnit (treeMatrix T G).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp (treeInject T G))

def cutL : Matrix (GhostI T G) (LinksI G P) ℂ :=
  (treeMatrix T G)⁻¹ * (τ)ᵀ

lemma cut_free : cutL T G * ℐ = 0 := by
  unfold cutL
  rw [Matrix.mul_assoc, inclusion_cross (fun j i => Ne.symm (disjoint T G i j)), Matrix.mul_zero]

lemma cut_left : cutL T G * gradientM T G = 1 := by
  rw [cutL, Matrix.mul_assoc]
  exact nonsing_inv_mul (treeMatrix T G) (tree_unit T G)

lemma identifies {I : Type} {F F' : Matrix I (LinksI G P) ℂ} (hJ : F * ℐ = F' * ℐ)
    (hR : F * τ = F' * τ) : F = F' := by
  ext i j
  rcases present T G j with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [← col_inclusion _ F, ← col_inclusion _ F', hJ]
  rw [← col_inclusion _ F, ← col_inclusion _ F', hR]

lemma spanning : ℐ * (ℐ)ᵀ + τ * (τ)ᵀ = 1 := by
  refine identifies T G ?_ ?_
  · simp_rw [Matrix.add_mul, Matrix.mul_assoc, inclusion_mul (free_inj T G),
      inclusion_cross (fun j i => Ne.symm (disjoint T G i j)), Matrix.mul_zero, Matrix.mul_one,
      Matrix.one_mul, add_zero]
  rw [Matrix.add_mul, Matrix.mul_assoc, inclusion_cross (disjoint T G), Matrix.mul_assoc,
    inclusion_mul (tree_inj T G), Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul, zero_add]

lemma identifies_R {I : Type} {F F' : Matrix I (LinksI G P) ℂ} (hJ : F * ℐ = F' * ℐ)
    (hR : F * gradientM T G = F' * gradientM T G) : F = F' := by
  let V : Matrix (LinksI G P) (GhostI T G) ℂ := ℐ * ((ℐ)ᵀ * gradientM T G)
  have he : gradientM T G = V + τ * treeMatrix T G := by
    unfold V treeMatrix
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul, spanning, Matrix.one_mul]
  have hv : F * V = F' * V := by
    unfold V
    rw [← Matrix.mul_assoc, hJ, Matrix.mul_assoc]
  rw [he, Matrix.mul_add, Matrix.mul_add, hv] at hR
  replace hR := add_left_cancel hR
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc] at hR
  refine identifies T G hJ ?_
  replace hR := congr_arg (· * (treeMatrix T G)⁻¹) hR
  rwa [Matrix.mul_assoc (F * τ), Matrix.mul_assoc (F' * τ), Matrix.mul_nonsing_inv _ (tree_unit T G),
    Matrix.mul_one, Matrix.mul_one] at hR

end YM.WilsonMS.Root
