import YM.WilsonMS.Top.ImageBlock

/-! # Intertwiners on the link orbits -/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Quo
open Function Filter Set Finset Matrix Lattice XSpace
open MS MS.Native Root Darboux Position
open scoped Topology

variable {P : Period} (T : P.Tree) (G : Gauge)

def chosen (P : Period) (G : Gauge) (e : LinksI G P) : SiteField G P.side :=
  (linkEquiv G P.side).symm (e.1.val, e.2)

def inverted (P : Period) (G : Gauge) (e : LinksI G P) : SiteField G P.side :=
  reflectedE G P.side (chosen P G e)

lemma chosen_inj (P : Period) (G : Gauge) : Injective (chosen P G) := fun i j h => by
  obtain he := (linkEquiv G P.side).symm.injective h
  exact Prod.ext (Subtype.ext (congr_arg Prod.fst he)) (show i.2 = j.2 from Prod.mk.inj he |>.2)

lemma inverts_link (w : SiteField G P.side) :
    linkEquiv G P.side (reflectedE G P.side w) =
      (P.reflect ((linkEquiv G P.side w).1), (linkEquiv G P.side w).2) :=
  rfl

lemma inverted_inj (P : Period) (G : Gauge) : Injective (inverted P G) :=
  (involE G P.side).injective.comp (chosen_inj P G)

lemma separate (P : Period) (G : Gauge) (i j) : chosen P G i ≠ inverted P G j := by
  intro h
  unfold inverted at h
  apply_fun (linkEquiv G P.side) at h
  unfold chosen at h
  rw [inverts_link, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  have hv : j.1.val = P.reflect i.1.val := by
    rw [show i.1.val = P.reflect j.1.val from congr_arg Prod.fst h, P.reflect_invol]
  exact absurd (hv ▸ j.1.property : P.Chosen (P.reflect i.1.val)) (by simp [i.1.property])

lemma covered (i : SiteField G P.side) : i ∈ Set.range (chosen P G) ∨ i ∈ Set.range (inverted P G) := by
  let x := linkEquiv G P.side i
  by_cases h : P.Chosen x.1
  · exact
      .inl
        ⟨(⟨x.1, h⟩, x.2), by
          unfold chosen
          rw [show (x.1, x.2) = x from rfl]
          exact Equiv.symm_apply_apply ..⟩
  refine .inr ⟨(⟨P.reflect x.1, by simp [h]⟩, x.2), (linkEquiv G P.side).injective ?_⟩
  unfold inverted chosen
  rw [inverts_link, Equiv.apply_symm_apply]
  dsimp only
  rw [P.reflect_invol]

/-- Restore the tensorial field on all links. All columns have squared
length **two** in these unnormalized coordinates. -/
def liftJ (P : Period) (G : Gauge) : Matrix (SiteField G P.side) (LinksI G P) ℂ :=
  inclusion (chosen P G) - inclusion (inverted P G)
local notation "J'" => liftJ P G
local notation "ℐ" => inclusion (chosen P G)
local notation "τ" => inclusion (inverted P G)
local notation "θE" => flipE G P.side

lemma jV (i j : LinksI G P) : J' (chosen P G i) j = if i = j then 1 else 0 := by
  unfold liftJ
  rw [Matrix.sub_apply, inclusion_else (inverted P G) _ j (Ne.symm (separate P G i j)), sub_zero]
  by_cases h : i = j
  · subst j
    rw [if_pos rfl]
    exact inclusion_at ..
  rw [if_neg h]
  exact inclusion_else _ _ _ ((chosen_inj P G).ne (Ne.symm h))

lemma jW (i j : LinksI G P) : J' (inverted P G i) j = -J' (chosen P G i) j := by
  rw [jV, liftJ, Matrix.sub_apply, inclusion_else _ _ _ (separate P G j i), zero_sub]
  apply congr_arg
  by_cases h : i = j
  subst j
  rw [if_pos rfl, inclusion_at]
  rw [if_neg h]
  exact inclusion_else _ _ _ ((inverted_inj P G).ne (Ne.symm h))

lemma lifted_norm : J'ᵀ * J' = (2 : ℂ) • 1 := by
  unfold liftJ
  rw [transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, inclusion_mul (chosen_inj ..),
    inclusion_mul (inverted_inj ..), inclusion_cross (separate P G),
    inclusion_cross (fun i j => Ne.symm (separate P G j i))]
  module

lemma mirror_lift : θE * J' = J' := by
  ext i j
  rw [Position.turnL]
  rcases covered G i with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [show reflectedE _ _ _ = inverted P G i from rfl, jW, neg_neg]
  rw [jW, show reflectedE G P.side (inverted P G i) = _ from involE G P.side _]

private lemma enoughJ {X : Type} (F Z : Matrix (SiteField G P.side) X ℂ) (h : ℐᵀ * F = ℐᵀ * Z)
    (hk : τᵀ * F = τᵀ * Z) : F = Z := by
  ext i j
  rcases covered G i with ⟨i, rfl⟩ | ⟨i, rfl⟩
  rw [← row_inclusion _ F, ← row_inclusion _ Z, h]
  rw [← row_inclusion _ F, ← row_inclusion _ Z, hk]

lemma projected : J' * J'ᵀ = 1 + θE := by
  apply enoughJ G
  · rw [← Matrix.mul_assoc, liftJ, Matrix.mul_sub, inclusion_mul (chosen_inj ..),
      inclusion_cross (separate P G), sub_zero, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one,
      transpose_sub, sub_eq_add_neg]
    congr 1
    ext i j
    rw [Root.row_inclusion, flipE, Matrix.neg_apply, Matrix.neg_apply, transpose_apply,
      Root.inclusion, Root.inclusion]
    unfold inverted
    simp only [show reflectedE G P.side (chosen P G i) = j ↔ reflectedE G P.side j = chosen P G i from
          (involE G P.side).eq_iff.trans eq_comm]
  rw [← Matrix.mul_assoc, liftJ, Matrix.mul_sub,
    inclusion_cross (fun j i => Ne.symm (separate P G i j)), inclusion_mul (inverted_inj ..),
    zero_sub, Matrix.neg_mul, Matrix.one_mul, transpose_sub, Matrix.mul_add, Matrix.mul_one,
    sub_eq_add_neg, neg_add_rev, neg_neg]
  congr 1
  ext i j
  rw [Root.row_inclusion, flipE, Matrix.neg_apply, Matrix.neg_apply, transpose_apply, Root.inclusion,
    Root.inclusion]
  unfold inverted
  simp only [(involE G P.side).injective.eq_iff, eq_comm]

lemma cancelJ {X : Type} {V W : Matrix (LinksI G P) X ℂ} (h : J' * V = J' * W) : V = W := by
  have hh := congr_arg (J'ᵀ * ·) h
  simp only [← Matrix.mul_assoc, lifted_norm, Matrix.smul_mul, Matrix.one_mul] at hh
  exact smul_right_injective _ (by norm_num : (2 : ℂ) ≠ 0) hh

lemma expands_basis (i : LinksI G P) (j : SiteField G P.side) :
    J' j i =
      (↑((Native.glow G (Site P.side)).seed (linkEquiv G P.side j) (liftedA P G (priv i))) : ℂ) := by
  rw [Native.glow, projector_k]
  rcases covered G j with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [jV]
    change _ = (↑(P.extend (priv i) j.1.val j.2) : ℂ)
    rw [P.extend_at]
    rcases i with ⟨i, a⟩
    rcases j with ⟨j, b⟩
    by_cases h : j = i <;> by_cases hx : b = a <;> simp [Native.priv, baseC, h, hx]
  rw [jW, jV]
  change _ = (↑(P.extend (priv i) (P.reflect j.1.val) j.2) : ℂ)
  rw [P.extend_reflect, P.extend_at]
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  by_cases h : j = i <;> by_cases hx : b = a <;> simp [Native.priv, baseC, h, hx]

lemma anti_origin : FFT.originP (Ax G) P.side * θE = -(FFT.originP (Ax G) P.side) := by
  ext ⟨i, x⟩ ⟨j, y⟩
  rw [turnR]
  unfold reflectedE
  dsimp only
  rw [FFT.origin_cell, Matrix.neg_apply, FFT.origin_cell]

lemma no_zero : FFT.originP (Ax G) P.side * J' = 0 := by
  let Z := FFT.originP (Ax G) P.side
  suffices h : (Z * J') + (Z * J') = 0 by linear_combination (norm := module) ((2 : ℂ)⁻¹) • h
  nth_rw 1 [← mirror_lift G]
  rw [← Matrix.mul_assoc, show Z * θE = -Z from anti_origin .., Matrix.neg_mul, neg_add_cancel]
end YM.WilsonMS.Quo
