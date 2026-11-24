import YM.WilsonMS.Top.LinkLift

/-! # Rooted vs mean-zero gauges in the tangent space

In particular, all normalization factors should work with the site measure
on the inversion quotient (careful at the fixed sites!). Do the calculation
exactly in terms of the pairing on the full `Site P.side`. Can keep
`T.root` arbitrary. -/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Quo
open Function Filter Set Finset Matrix Complex Lattice XSpace
open MS MS.Native MS.Orbit Root Position
open scoped Topology

variable {P : Period} (T : P.Tree) (G : Gauge)

def liftN : Matrix (GaugeField G P.side) (GhostI T G) ℂ := fun x y =>
  ((based T G (priv y) (P.vertex x.2) x.1 : ℝ) : ℂ)
local notation "G₀" => FFT.originP G.ColorIndex P.side
local notation "B'" => liftN T G
local notation "θ" => flipU G P.side

def averageM : Matrix (GaugeField G P.side) (GhostI T G) ℂ :=
  (1 - G₀) * B'
local notation "M'" => averageM T G
local notation "L'" => straightL G P.side
local notation "J'" => liftJ P G

section
variable {X : Type}

def selected (x : P.Vertex) : P.Sites :=
  (P.vertex_surjective x).choose

lemma selecting (x : P.Vertex) : P.vertex (selected x) = x :=
  (P.vertex_surjective x).choose_spec

def subtracts (V : Matrix (GaugeField G P.side) X ℂ) : Matrix (GhostI T G) X ℂ := fun j x =>
  V (j.2, selected j.1.val) x - V (j.2, selected T.root) x

lemma B_entry (V : Matrix (GhostI T G) X ℂ) (c : G.ColorIndex) (i : P.Sites) (x : X) :
    (B' * V) (c, i) x = extendedParameter T G (fun j => V j x) (P.vertex i) c := by
  rw [Matrix.mul_apply, ← eval_parameter]
  rfl

lemma arithmeticMean (V : Matrix (GaugeField G P.side) X ℂ) (c : G.ColorIndex) (i : P.Sites) (x : X) :
    (G₀ * V) (c, i) x = scaleZ P.side * ∑ k : P.Sites, V (c, k) x := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, sum_eq_single_of_mem c (mem_univ _)]
  · simp_rw [FFT.origin_cell]
    simp only [ite_true, Finset.mul_sum]
  intro b _ hb
  simp_rw [FFT.origin_cell, if_neg (Ne.symm hb), zero_mul, sum_const_zero]

lemma constants_mean (V : Matrix (GaugeField G P.side) X ℂ)
    (hc : ∀ x y : GaugeField G P.side, x.1 = y.1 → V x = V y) : G₀ * V = V := by
  ext ⟨c, i⟩ x
  rw [arithmeticMean]
  simp_rw [show ∀ j : P.Sites, V (c, j) x = V (c, i) x from fun j =>
      congr_fun (hc (c, j) (c, i) rfl) x]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul, ← mul_assoc]
  rw [show (Fintype.card P.Sites : ℂ) = brightness P.side from ?_, lightW, one_mul]
  simp [XSpace.Period.Sites, volumeFactor]

lemma cancellationM (V : Matrix (GhostI T G) X ℂ) : subtracts T G (M' * V) = V := by
  ext ⟨⟨i, hi⟩, c⟩ x
  unfold averageM
  rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
  unfold subtracts
  rw [Matrix.sub_apply, Matrix.sub_apply, arithmeticMean, arithmeticMean, sub_sub_sub_cancel_right,
    B_entry, B_entry, selecting, selecting, extendedParameter, dif_pos hi, extendedParameter,
    dif_neg (by simp), sub_zero]

lemma authority {V W : Matrix (GhostI T G) X ℂ} (he : M' * V = M' * W) : V = W := by
  rw [← cancellationM _ _ V, he, cancellationM]

lemma pins {U : Matrix (GaugeField G P.side) X ℂ} (hp : θ * U = U) (he : G₀ * U = 0) :
    M' * subtracts T G U = U := by
  let W := Matrix.of (fun (i : GaugeField G P.side) x => U (i.1, selected T.root) x)
  have hv (c : G.ColorIndex) (p : P.Sites) : U (c, selected (P.vertex p)) = U (c, p) := by
    funext x
    obtain hh := (P.vertex_eq_iff p _).mp (selecting (P.vertex p) |>.symm)
    cases hh with
    | inl h => rw [h]
    | inr h =>
      rw [h,
        show U (c, -p) x = _ from
          (turnU G P.side U (c, p) x).symm.trans (congr_fun (congr_fun hp _) x)]
  have hh : B' * subtracts T G U = U - W := by
    ext ⟨c, p⟩ x
    rw [B_entry, Matrix.sub_apply, extendedParameter]
    split
    next h =>
      unfold subtracts
      dsimp only
      rw [hv]
      rfl
    next h =>
      have hy : P.vertex p = T.root := not_not.mp h
      specialize hv c p
      rw [hy] at hv
      change 0 = U (c, p) x - U (c, selected T.root) x
      rw [congr_fun hv, sub_self]
  rw [averageM, Matrix.mul_assoc, hh, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, he,
    constants_mean G W
      (fun x y h => by
        ext i
        unfold W
        rw [of_apply, of_apply, h])]
  abel
end

lemma B_flip : θ * B' = B' := by
  ext ⟨i, v⟩ j
  rw [turnU]
  unfold liftN reflectedG
  dsimp only
  rw [P.vertex_neg]

def landL : Matrix (GhostI T G) (LinksI G P) ℂ :=
  subtracts T G (L' * J')

lemma land_eq : M' * landL T G = L' * J' := by
  apply pins
  · rw [← Matrix.mul_assoc, reachesE, Matrix.mul_assoc, mirror_lift]
  rw [← Matrix.mul_assoc, straight_mean, Matrix.zero_mul]

end YM.WilsonMS.Quo
