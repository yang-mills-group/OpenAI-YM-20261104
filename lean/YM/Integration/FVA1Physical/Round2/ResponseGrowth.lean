import YM.Integration.FVA1Physical.Round2.PosteriorMean

/-! The sparse held-derivative cost grows only polynomially in the actual
inverse coupling. Its exponent and prefactor are independent of the period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Lattice RG Wilson Push.Local.Kernel
open scoped Classical Matrix.Norms.Frobenius

def invDegree : ℕ → ℕ
  | 0 => 0
  | n+1 => 2*invDegree n+1

def responseDegree (k : ℕ) := k + k*invDegree k

private theorem inv_nonnegative (k : ℕ) {x : ℝ} (hx : 0≤x) (j : ℕ) : 0≤ invRate k x j := by
  induction j with
  | zero => simp [invRate]
  | succ j ih => rw [invRate]; positivity

private theorem inv_mono (k : ℕ) {x y : ℝ} (hx : 0≤x) (hxy : x≤y) (j : ℕ) :
    invRate k x j≤ invRate k y j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [invRate]
    have hY := inv_nonnegative k (hx.trans hxy) j
    have hX := inv_nonnegative k hx j
    gcongr

private theorem inv_scale (k : ℕ) (x a : ℝ) (j : ℕ) :
    invRate k (x*a) j = invRate k x j * a^invDegree j := by
  induction j with
  | zero => simp [invRate,invDegree]
  | succ j ih => simp only [invRate,invDegree,ih,pow_succ,two_mul,pow_add]; ring

theorem responsePrice_nonnegative (G : Gauge) (u : ℝ) (k j : ℕ) {r : ℝ} (hr : 0≤r) :
    0 ≤ responsePrice G u k j r := by
  have h := zero_le_one.trans (noiseFactor_ge G u k j hr)
  exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg h k) (inv_nonnegative _ (pow_nonneg h k) _))

theorem sparse_price_polynomial (G : Gauge) {u a b r : ℝ} (k j M : ℕ) (hr : 0≤r)
    (ha : 0≤a) (hb : 1≤b) (hU : |u|≤a*b) (hj : j≤M) :
    responsePrice G u k j r ≤ responsePrice G a k M r * b^responseDegree k := by
  let P := pairingNorm G * (‖(1:G.Mat)‖ * (1+G.colorScale*r)^k)
  have h0 : 0≤P := mul_nonneg (pairingNorm_nonneg G) (mul_nonneg (norm_nonneg _)
    (pow_nonneg (add_nonneg zero_le_one (mul_nonneg G.colorScale_pos.le hr)) _))
  have score : scorePrice G u k j r ≤ scorePrice G a k M r * b := by
    have e := mul_le_mul (Nat.cast_le.mpr hj : (j:ℝ)≤M) hU (abs_nonneg _) (Nat.cast_nonneg _)
    have ee := mul_le_mul_of_nonneg_right e h0
    simp only [scorePrice,abs_of_nonneg ha]
    dsimp only [P] at ee
    linarith only [ee,hb]
  let X := noiseFactor G u k j r
  let Y := noiseFactor G a k M r
  have hX : 0≤X := zero_le_one.trans (noiseFactor_ge G u k j hr)
  have he : X≤Y*b := (mul_le_mul_of_nonneg_left score (by positivity : 0≤(2:ℝ)^k)).trans_eq (by
    dsimp only [Y,noiseFactor]; ring)
  have hc : X^k≤Y^k*b^k := (pow_le_pow_left₀ hX he k).trans_eq (mul_pow ..)
  have hY : 0≤Y^k*b^k := (pow_nonneg hX k).trans hc
  have hI := inv_mono k (pow_nonneg hX k) hc k
  have pay := mul_le_mul hc hI (inv_nonnegative k (pow_nonneg hX k) k) hY
  have ans := mul_le_mul_of_nonneg_left pay (by positivity : 0≤(2:ℝ)^k)
  rw [inv_scale] at ans
  apply ans.trans_eq
  dsimp only [responsePrice,responseDegree,X,Y]
  rw [pow_add,pow_mul]
  ring
end YM.Integration.FVA1Physical.Round2
