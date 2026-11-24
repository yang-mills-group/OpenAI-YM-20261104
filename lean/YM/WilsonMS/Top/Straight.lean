import YM.WilsonMS.Top.MomentumProjector

/-! # Identities at this *finite* torus, including exceptional-momentum modifications

Don't use a large-volume approximation to justify the gauge change!
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Position
open Function Finset Filter Set Matrix Complex Lattice
open MS MS.Orbit MS.Orbit.Cog MS.Koszul MS.Plane MS.Bare MS.Native
open MS.Book MS.Cylinder MS.Landau MS.Latch MS.City MS.Swirl MS.Swirl.Near MS.Tone
open FFT

variable (G : Gauge) (n : Side)
local notation "A'" => CA G n
local notation "L'" => LK G n
local notation "H'" => angularP G n
local notation "D'" => angularD G n
local notation "R'" => FFT.rev (Ax G) n
local notation "WA" => FFT.forward (Ax G) n
local notation "WC" => FFT.forward (G.ColorIndex) n
local notation "WM" => FFT.backward (Ax G) n
local notation "WU" => FFT.backward (G.ColorIndex) n
local notation "ν" => scaleZ n
local notation "Λ" => brightness n

def straightA : Matrix (SiteField G n) (SiteField G n) ℂ :=
  WA * A' * WAᵀ

def straightL : Matrix (GaugeField G n) (SiteField G n) ℂ :=
  WC * L' * WAᵀ
local notation "A0" => straightA G n
local notation "L0" => straightL G n
local notation "S0" => FFT.originP (Ax G) n
local notation "G0" => FFT.originP (G.ColorIndex) n

lemma straight_left : L0 * fullD G n = 1 - G0 := by
  let V := fullD G n
  have he : L0 * V * WC = WC * FFT.exclude0 G.ColorIndex n := by
    rw [straightL, Matrix.mul_assoc (WC * L'), Matrix.mul_assoc (WC * L'), Matrix.mul_assoc,
      show L' * (WAᵀ * V * WC) = _ from angular_left G n]
  unfold FFT.originP
  rw [← angular_left, Matrix.mul_sub, Matrix.mul_one, angular_left, Matrix.sub_mul, forward_inverse,
    sub_sub_cancel, ← he, Matrix.mul_assoc (L0 * V), forward_inverse, Matrix.mul_one]

lemma straight_inverse : A0 * fullH G n + fullD G n * L0 = 1 - S0 := by
  let H := fullH G n
  let D := fullD G n
  let P := A0 * H
  let Q := D * L0
  have he : WM * P * WA = A' * H' := by
    unfold P straightA
    have hp : A' * H' = A' * (WAᵀ * H * WA) := rfl
    rw [hp]
    simp only [← Matrix.mul_assoc, backward_inverse, Matrix.one_mul]
  have hf : WM * Q * WA = R' * (D' * L') * R' := by
    have hp : WM * (D * WC) = ν • (R' * D') := by
      rw [inverse_by_rev, show D' = WAᵀ * D * WC from rfl]
      simp only [← Matrix.mul_assoc, Matrix.smul_mul]
    change WM * (D * (WC * L' * WAᵀ)) * WA = _
    rw [← Matrix.mul_assoc D, ← Matrix.mul_assoc D, ← Matrix.mul_assoc WM, ← Matrix.mul_assoc WM, hp,
      Matrix.mul_assoc _ WAᵀ, FFT.gram]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      show Λ * ν = 1 from (mul_comm ..) |>.trans (lightW ..), one_smul, Matrix.mul_assoc]
  change P + Q = _
  have ht : WM * (P + Q) * WA = FFT.exclude0 (Ax G) n := by
    rw [Matrix.mul_add, Matrix.add_mul, he, hf, angular_inverse]
  rw [FFT.originP, ← ht, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, forward_inverse,
    sub_sub_cancel, ← Matrix.mul_assoc WA, ← Matrix.mul_assoc WA, forward_inverse, Matrix.one_mul,
    Matrix.mul_assoc, forward_inverse, Matrix.mul_one]

lemma straight_transverse : L0 * A0 = 0 := by
  unfold straightL straightA
  rw [← Matrix.mul_assoc _ _ WAᵀ, ← Matrix.mul_assoc _ _ A', Matrix.mul_assoc _ WAᵀ WA, FFT.gram,
    Matrix.mul_smul, Matrix.mul_assoc WC, Matrix.smul_mul, Matrix.mul_assoc, angular_transverse]
  simp

section

private lemma pay_harmonic (a : GaugeField G n) : ∀ p : SiteField G n, a.2 = 0 → LK G n a p = 0 := by
  rintro ⟨⟨i, j⟩, p⟩ hp
  rcases a with ⟨k, x⟩
  dsimp only at hp
  subst x
  by_cases hh : p = -(0 : Site n)
  subst p
  simp_rw [L_matrix, mu_zero]
  simp
  exact LF_off _ _ _ _ _ _ hh

private lemma harmonic_off (a : SiteField G n) :
    ∀ p : GaugeField G n, p.2 = 0 → angularD G n a p = 0 := by
  rintro ⟨c, q⟩ h
  rcases a with ⟨⟨i, j⟩, p⟩
  dsimp only at h
  subst q
  by_cases hp : p ≠ -(0 : Site n)
  swap
  · rw [not_not] at hp
    subst p
    rw [D_matrix]
    simp [wi, ξ_zero, Momentum.wave, Momentum.theta]
  have hv : (0 : Site n) ≠ -p := fun h => hp (by rw [h, neg_neg])
  exact neg_neg p ▸ (show angularD G n ((i, j), - -p) (c, 0) = 0 from DF_off G n (-p) 0 _ c hv)

lemma straight_mean : G0 * L0 = 0 := by
  let V := 1 - FFT.exclude0 G.ColorIndex n
  have he a i j : V (i, a) j = if a = 0 then (1 : Matrix _ _ ℂ) (i, a) j else 0 := by
    unfold V
    rw [Matrix.sub_apply, FFT.exclude0]
    dsimp only
    split <;> simp
  have hx : V * L' = 0 := by
    ext ⟨i, a⟩ j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    by_cases hp : a = 0
    swap
    · rw [he, if_neg hp, zero_mul]
    subst a
    rw [he, if_pos rfl, one_apply]
    split
    next h => rw [pay_harmonic G n k j (by rw [← h]), mul_zero]
    next h => rw [zero_mul]
  change WC * V * WU * (WC * L' * WAᵀ) = _
  rw [← Matrix.mul_assoc _ _ WAᵀ, ← Matrix.mul_assoc _ _ L', Matrix.mul_assoc _ WU, backward_inverse,
    Matrix.mul_one, Matrix.mul_assoc WC, hx, Matrix.mul_zero, Matrix.zero_mul]

lemma grad_zero_mode : fullD G n * G0 = 0 := by
  let V := 1 - FFT.exclude0 G.ColorIndex n
  have he (x y : GaugeField G n) : V x y = if x.2 = 0 then (1 : Matrix _ _ ℂ) x y else 0 := by
    unfold V
    rw [Matrix.sub_apply, FFT.exclude0]
    split <;> simp
  have hx : D' * V = 0 := by
    ext i j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    by_cases hp : k.2 = 0
    · rw [harmonic_off G n i k hp, zero_mul]
    rw [he, if_neg hp, mul_zero]
  have hh : WMᵀ * D' = fullD G n * WC := by
    unfold angularD
    simp only [← Matrix.mul_assoc, ← transpose_mul, FFT.forward_inverse, transpose_one,
      Matrix.one_mul]
  change fullD G n * (WC * V * WU) = 0
  rw [← Matrix.mul_assoc (fullD G n), ← Matrix.mul_assoc (fullD G n), ← hh, Matrix.mul_assoc WMᵀ, hx,
    Matrix.mul_zero, Matrix.zero_mul]
end
end YM.WilsonMS.Position
