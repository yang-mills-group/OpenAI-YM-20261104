import YM.FVA2.Fourier.Transform
import YM.MS.Tone.Curl

/-! # Reading the lattice hats in the MS kernel -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Fourier
open Function Set Finset
open YM.MS YM.MS.Koszul YM.MS.Plane YM.MS.Cylinder YM.MS.Orbit YM.MS.City
open YM.MS.Landau YM.MS.Tone Tone.Frame YM.MS.Momentum
open YM.Lattice
open Complex (I)
open scoped BigOperators Matrix
variable {G : Gauge} {n : Side}

/-- Link midpoint phase convention as used in Bass. -/
def midpoint (p : Site n) (i : Axis) : ℂ := bill (Coord p) (z i)
def freq (p : Site n) (i : Axis) : ℂ := ↑(wave (Coord p) i)

lemma scalar_flag (h : Bool) (c : G.ColorIndex) (p : QP) : flag ((none,h),c) p = 1 := by
  unfold flag weightψ; exact right0 _
lemma vector_flag (h : Bool) (c : G.ColorIndex) (p : Site n) (i : Axis) :
    flag ((some i,h),c) (Coord p) = midpoint p i := rfl
lemma midpoint_ne (p : Site n) (i : Axis) : midpoint p i ≠ 0 := nonz _ _
lemma flag_inverse (x : BH G) (p : QP) : flag x (-p) = (flag x p)⁻¹ :=
  Tone.opp ..

lemma midpoint_diff (p : Site n) (i : Axis) :
    midpoint p i - (midpoint p i)⁻¹ = I * freq p i := by
  unfold midpoint; rw [← Tone.inverse, s_wave]; rfl
lemma step_phase (p : Site n) (i : Axis) : Bloch.cell p (step i) = midpoint p i ^ 2 := by
  calc
    _ = bill (embed (step i)) (Coord p) := by rw [dual_cell, wrap_step]
    _ = _ := by rw [rights, centr, Tone.rightadd, pow_two]; rfl
lemma grad_hat (p : Site n) (i : Axis) :
    1 - Bloch.cell p (step i) = -(I * freq p i) * midpoint p i := by
  rw [step_phase, ← midpoint_diff, neg_mul, sub_mul,
    inv_mul_cancel₀ (midpoint_ne p i), neg_sub, pow_two]
lemma div_hat (p : Site n) (i : Axis) :
    1 - (Bloch.cell p (step i))⁻¹ = I * freq p i * (midpoint p i)⁻¹ := by
  rw [step_phase, ← midpoint_diff, sub_mul, mul_inv_cancel₀ (midpoint_ne p i),
    ← inv_pow, pow_two (midpoint p i)⁻¹]

lemma wave_some {p : Site n} (hp : p ≠ 0) : ∃ i : Axis, freq p i ≠ 0 := by
  obtain ⟨i,h⟩ := Bloch.step_picks p hp
  refine ⟨i,fun he => h ?_⟩
  apply Eq.symm
  exact sub_eq_zero.mp (by rw [grad_hat, he]; simp)

lemma wave_sq_ne {p : Site n} (hp : p ≠ 0) : ((wave (Coord p)).sq : ℂ) ≠ 0 := by
  intro H
  obtain ⟨i,h⟩ := wave_some hp
  apply h
  have H' : (wave (Coord p)).sq = 0 := by exact_mod_cast H
  have he : wave (Coord p) i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j (_ : j ∈ (Finset.univ : Finset Axis)) =>
       sq_nonneg (wave (Coord p) j)).mp H' i (Finset.mem_univ _)
  unfold freq; rw [show wave (Coord p) i = 0 from by nlinarith only [he], Complex.ofReal_zero]

@[simp] theorem freq_zero (i : Axis) : freq (0 : Site n) i = 0 := by simp [Orbit.ξ_zero, freq, wave, theta]

lemma freq_square (p : Site n) : ∑ i, freq p i * freq p i = ↑(wave (Coord p)).sq := by
  simp [Momentum.sq, freq, pow_two]
lemma precision_f (p : Site n) (i j : Axis) :
    (precision i j (wave (Coord p)) : ℂ) =
      (if i=j then ↑(wave (Coord p)).sq else 0) - freq p i * freq p j := by
  simp only [precision, Landau.delta, freq, Complex.ofReal_sub, Complex.ofReal_mul]
  split <;> simp
lemma trans_freq (p : Site n) (i : Axis) :
    ∑ j, (precision i j (wave (Coord p)) : ℂ) * freq p j = 0 := by
  simp only [precision_f, sub_mul, Finset.sum_sub_distrib, ← freq_square, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [mul_assoc (freq p i), ← Finset.mul_sum, mul_comm _ (freq p i), sub_self]

-- Inversion sign. All are based, not midpoint.
def shiftBase (a : BH G) : Site n := a.1.1.elim 0 Lattice.step
def sgn (a : BH G) : ℂ := if a.1.1.isSome then -1 else 1
lemma sgn_two (a : BH G) : sgn a * sgn a = 1 := by unfold sgn; split <;> simp
lemma switch_at (a : BH G) (p : Site n) :
    switch (a,Coord p) = sgn a * (Bloch.cell p (shiftBase a))⁻¹ := by
  rcases a with ⟨⟨_|i,h⟩,c⟩
  · change 1 * (flag ((none,h),c) (-Coord p))^2 = 1 * (Bloch.cell p 0)⁻¹
    simp [scalar_flag]
  change -1 * (flag ((some i,h),c) (-Coord p))^2 = -1 * (Bloch.cell p (step i))⁻¹
  rw [flag_inverse, vector_flag, step_phase, inv_pow]

lemma inv_location (p x : Site n) (a : BH G) :
    sgn a * Bloch.cell p (-x-shiftBase a) = Bloch.cell (-p) x * switch (a,Coord p) := by
  rw [sub_eq_add_neg, Bloch.cell_add, Bloch.cell_inverse, Bloch.cell_inverse,
    Bloch.cell_duality (-p) x, Bloch.cell_inverse, Bloch.cell_duality x p,
    switch_at, mul_left_comm]
end YM.FVA2.Fourier
