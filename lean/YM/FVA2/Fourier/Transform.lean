import YM.FVA2.Wick.Pull
import YM.MS.Orbit.Mat

/-!
# Fourier coordinates on the MS torus

Finite DFT for all site, link, and antifield modes. This Fourier unpacking is **based**, not
midpoint; the latter is used at an intermediate step by MS but not in `Endμ`; thus there are no
extra half phases in `toSite`. It hasn't projected to equivariant fields yet. Both indices use
`FixedMode`; one a position, one a momentum.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Fourier
open Function Set Finset
open YM.MS YM.MS.Koszul YM.MS.Plane YM.MS.Cylinder YM.MS.Landau YM.MS.City YM.MS.Orbit
open YM.Lattice
open Complex (conjCLE)
open scoped BigOperators Matrix
variable {G : Gauge} {n : Side}

/-- Evaluate the Fourier series at all lattice positions (based). Pos-index rows. -/
def toSite (G : Gauge) (n : Side) : Matrix (FixedMode G n) (FixedMode G n) ℂ :=
  Matrix.of fun a b => if a.1=b.1 then Bloch.cell b.2 a.2 else 0

/-- Extract the Fourier coefficients. Momentum-index rows. -/
def toFreq (G : Gauge) (n : Side) : Matrix (FixedMode G n) (FixedMode G n) ℂ :=
  Matrix.of fun a b => if a.1=b.1 then scaleZ n * (Bloch.cell a.2 b.2)⁻¹ else 0

lemma scale_val (n : Side) : scaleZ n = ((n.val : ℂ)^4)⁻¹ := by
  simp only [scaleZ, νt, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_natCast]

lemma scale_ne (n : Side) : scaleZ n ≠ 0 := by rw [scale_val]; exact inv_ne_zero (pow_ne_zero _ (Bloch.side_ne n))

lemma toSite_eq (a b : FixedMode G n) :
    toSite G n a b = if a.1=b.1 then Bloch.cell b.2 a.2 else 0 := rfl
lemma toFreq_eq (a b : FixedMode G n) :
    toFreq G n a b = if a.1=b.1 then scaleZ n * (Bloch.cell a.2 b.2)⁻¹ else 0 := rfl
lemma unpack_pack (G : Gauge) (n : Side) : toSite G n * toFreq G n = 1 := by
  ext ⟨a,p⟩ ⟨b,q⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type (α₁:=BH G), toSite_eq, toFreq_eq,
    Matrix.one_apply, Prod.mk.injEq]
  by_cases h : a=b
  · subst b
    rw [Finset.sum_eq_single a]
    · simp only [if_true, true_and]
      simp_rw [show ∀ i, Bloch.cell i p * (scaleZ n * (Bloch.cell i q)⁻¹) =
                       scaleZ n * (Bloch.cell p i * (Bloch.cell q i)⁻¹) from fun i => by
        rw [Bloch.cell_duality i p, Bloch.cell_duality i q, mul_left_comm]]
      rw [← Finset.mul_sum, Bloch.orthogonal, scale_val]; split_ifs
      · exact inv_mul_cancel₀ (pow_ne_zero _ (Bloch.side_ne n))
      exact mul_zero _
    · intro i _ H; simp only [if_neg H, mul_zero, Finset.sum_const_zero]
    exact fun hi => (hi (Finset.mem_univ _)).elim
  rw [if_neg fun H => h H.1]
  exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by split_ifs with h₁ h₂ <;> simp_all

lemma pack_unpack (G : Gauge) (n : Side) : toFreq G n * toSite G n = 1 :=
  mul_eq_one_comm.mpr (unpack_pack G n)

lemma unpack_at (v : FixedMode G n → ℂ) (a : BH G) (x : Site n) :
    (toSite G n *ᵥ v) (a,x) = ∑ p : Site n, Bloch.cell p x * v (a,p) := by
  unfold Matrix.mulVec dotProduct
  simp only [Fintype.sum_prod_type (α₁:=BH G), toSite_eq]
  rw [Finset.sum_eq_single a]
  · simp
  · intro i _ hi; simp [Ne.symm hi]
  exact fun hi => (hi (Finset.mem_univ _)).elim
lemma pack_at (v : FixedMode G n → ℂ) (a : BH G) (p : Site n) :
    (toFreq G n *ᵥ v) (a,p) = scaleZ n * ∑ x : Site n, (Bloch.cell p x)⁻¹ * v (a,x) := by
  unfold Matrix.mulVec dotProduct
  simp only [Fintype.sum_prod_type (α₁:=BH G), toFreq_eq]
  rw [Finset.sum_eq_single a]
  · simp only [if_true, mul_assoc, Finset.mul_sum]
  · intro i _ hi; simp [Ne.symm hi]
  exact fun hi => (hi (Finset.mem_univ _)).elim

lemma unpack_tie (G : Gauge) (n : Side) : Tie σbranch σbranch (toSite G n)ᵀ := by
  intro i j h; apply congr_arg Landau.parity; by_contra he; exact h (if_neg he)
lemma pack_tie (G : Gauge) (n : Side) : Tie σbranch σbranch (toFreq G n)ᵀ := by
  intro i j h; apply congr_arg Landau.parity; by_contra he; exact h (if_neg he)
end YM.FVA2.Fourier
