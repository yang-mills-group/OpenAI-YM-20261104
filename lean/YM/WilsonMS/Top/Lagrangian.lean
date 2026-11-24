import YM.WilsonMS.Top.LandPropagator

/-! # Projectors needed for the harmonic-ghost adjustment -/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Quo
open Function Filter Set Finset Matrix Complex Lattice XSpace
open MS MS.Orbit MS.Bare MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.Native Root Position Darboux
open MS.Orbit.Cog MS.Swirl
open scoped Topology ContDiff Matrix.Norms.Frobenius

section dar
variable {A E I J X U : Type}

def legs (S Z : Matrix A I ℂ) (L : Matrix E J ℂ) : Matrix (Letters A E) (Letters I J) ℂ
  | .inl (.inl i), .inl (.inl j) => S i j
  | .inr (.inl i), .inr (.inl j) => Z i j
  | .inl (.inr i), .inl (.inr j) => L i j
  | _, _ => 0

lemma legs_tie (S Z : Matrix A I ℂ) (L : Matrix E J ℂ) : Tie (parity) parity ((legs S Z L)ᵀ) := by
  rintro ((x | x) | (x | x)) ((y | y) | (y | y)) <;> simp [legs, parity]
variable (S Z : Matrix A I ℂ) (L : Matrix E J ℂ) [Fintype I] [Fintype J]

lemma followed (T U' : Matrix I X ℂ) (P : Matrix J U ℂ) :
    legs S Z L * legs T U' P = legs (S * T) (Z * U') (L * P) := by
  ext ((x | x) | (x | x)) ((y | y) | (y | y)) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, legs, Letters]

lemma chill_induced (C : Matrix I I ℂ) (G : Matrix J I ℂ) (x y : Letters A E) :
    Chill (induce (legs S Z L) (propagator C G)) x y =
      Darboux.covariance (S * C * Sᵀ) (L * G * Zᵀ) x y := by
  let P := propagator C G
  let V := legs S Z L
  unfold Chill
  rw [induce_value]
  have h :
    (2 : ℂ) * (∑ j : Letters I J, ∑ i : Letters I J, V x i * P i j * V y j) =
      ∑ j : Letters I J, ∑ i : Letters I J, V x i * Chill P i j * V y j := by
    simp_rw [Finset.mul_sum]
    exact
      Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => by
          unfold Chill
          ring
  rw [h]
  simp_rw [show ∀ i j, Chill P i j = _ from fun i j => correlation (C := C) (L := G) i j]
  unfold V
  rcases x with (x | x) | (x | x) <;> rcases y with (y | y) | (y | y) <;>
    simp [legs, Darboux.covariance, Letters, Matrix.mul_apply, Fintype.sum_sum_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
end dar

variable {P : Period} (T : P.Tree) (G : Gauge)
local notation "E" => LinksI G P
local notation "U" => GhostI T G
local notation "M'" => Root.Mode T G
local notation "gp" => gradientM T G
local notation "L" => landL T G
local notation "Y" => landC P G
local notation "C'" => propagator (landC P G) (landL T G)

def waveQ : Matrix (E) (E) ℂ :=
  1 - gp * L

def antiK : Matrix (E) (E) ℂ :=
  (gp * L)ᵀ

/-- Project to the Landau tangent plane. -/
def toLand : Matrix (Root.Mode T G) (Root.Mode T G) ℂ :=
  legs (waveQ T G) (antiK T G) (1 : Matrix (GhostI T G) (GhostI T G) ℂ)

def discard : Matrix (M') (M') ℂ :=
  legs 1 1 1

lemma absorbs : discard T G * toLand T G = toLand T G := by
  rw [discard, toLand, followed]
  simp

lemma discard_wire : Tie (dg T G) (dg T G) (discard T G)ᵀ :=
  legs_tie _ _ _

lemma plane_wire : Tie (dg T G) (dg T G) (toLand T G)ᵀ :=
  legs_tie _ _ _

lemma prop_invariant : induce (toLand T G) C' = C' := by
  have ht := Quo.split T G
  let F := waveQ T G
  let Q := antiK T G
  have he : F * Y = Y := by
    unfold F waveQ
    rw [Matrix.sub_mul, Matrix.mul_assoc, perpendicular, Matrix.mul_zero, Matrix.one_mul, sub_zero]
  have hx : (1 : Matrix U U ℂ) * L * Qᵀ = L := by
    unfold Q antiK
    rw [Matrix.one_mul, transpose_transpose, ← Matrix.mul_assoc, ht.left, Matrix.one_mul]
  have hf : F * Y * Fᵀ = Y := by
    rw [he]
    simpa only [transpose_mul, ht.symmC] using congr_arg transpose he
  funext x y
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  change Chill _ x y = Chill _ x y
  rw [toLand, chill_induced F Q _ _ L, hx, hf, correlation]

section

local notation "n" => P.side
local notation "J'" => liftJ P G

def location (S : Matrix (GaugeField G P.side) (GhostI T G) ℂ) :
    Matrix (FixedMode G P.side) (Root.Mode T G) ℂ := fun x j =>
  legs (liftJ P G) (liftJ P G) S ((eIso G P.side).symm x) j

lemma locationF (S : Matrix (GaugeField G P.side) (GhostI T G) ℂ) (x y) :
    location T G S (includeF G n x) y = legs J' J' S x y := by
  rw [location, show (eIso G P.side).symm (includeF G n x) = x from Equiv.symm_apply_apply ..]

lemma location_tie (S : Matrix (GaugeField G P.side) (GhostI T G) ℂ) :
    Tie σbranch (dg T G) (location T G S)ᵀ := by
  intro i j he
  obtain ⟨i, rfl⟩ := (eIso G P.side).surjective i
  rw [transpose_apply, show location T G S ((eIso G P.side) i) j = _ from locationF T G S i j] at he
  rw [← (show parity i = dg T G j from legs_tie J' J' S i j he)]
  rcases i with (i | i) | (i | i) <;> rfl

/-- Identify the *actual* MS finite kernel (as read in position Fourier)
with the lifted based Landau kernel, including the averaging on the root gauges
and the singular-site reflection convention. -/
lemma folding : induce (location T G (averageM T G)) C' = foldedK G n := by
  let C := location T G (averageM T G)
  let X := legs J' J' (averageM T G)
  funext x y
  obtain ⟨a, rfl⟩ := (eIso G P.side).surjective x
  obtain ⟨b, rfl⟩ := (eIso G P.side).surjective y
  have he : induce C C' (includeF G n a) (includeF G n b) = induce X C' a b := by
    unfold C X
    simp_rw [induce_value, locationF]
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  change Chill _ (includeF G n a) (includeF G n b) = Chill _ (includeF G n a) (includeF G n b)
  rw [image_chill, Chill, he]
  change Chill (induce X C') a b = _
  rw [chill_induced J' J' _ _ _, gram_image, longitudinal_image T G]
end
end YM.WilsonMS.Quo
