import YM.Integration.FVA1Physical.Round2.SpatialFieldReserve
import YM.Push.STATIONARY_UNIFORM.Array

/-! A shrinking spatial exponent pays a polynomial in its inverse width,
uniformly in torus size. The actual primary coordinate count includes face
orientation and color at each site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Lattice Finset MSbar.Heath MSbar.Whisk Push.Uniform
open scoped Classical BigOperators
variable {n : Side}

theorem torus_radial_price {a : ℝ} (ha : 0 < a) (b : Site n) :
    (∑ i:Site n,Real.exp (-a*separation b i)) ≤
      (2*(⌈a⁻¹⌉₊:ℝ)+1)^4 * meter 1 := by
  let B:=⌈a⁻¹⌉₊
  have pos : 0 < B := Nat.ceil_pos.mpr (inv_pos.mpr ha)
  have one : 1 ≤ a*(B:ℝ) := by
    calc 1 = a*a⁻¹ := (mul_inv_cancel₀ ha.ne').symm
         _ ≤ a*(B:ℝ) := mul_le_mul_of_nonneg_left (Nat.le_ceil _) ha.le
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (wick_pays (r:=1) zero_lt_one B pos b)
  let d:=separation b i
  have cut : (↑(d/B):ℝ)*B ≤ d := by exact_mod_cast Nat.div_mul_le_self d B
  have scaled : (↑(d/B):ℝ) ≤ a*d := by
    calc (↑(d/B):ℝ) ≤ (↑(d/B):ℝ)*(a*B) :=
             le_mul_of_one_le_right (Nat.cast_nonneg _) one
         _ = a*((↑(d/B):ℝ)*B) := by ring
         _ ≤ a*d := mul_le_mul_of_nonneg_left cut ha.le
  change Real.exp (-a*(d:ℝ)) ≤ Real.exp (-(1:ℝ)*(↑(d/B):ℝ))
  exact Real.exp_le_exp.mpr (by linarith only [scaled])

private theorem primary_sum (G : Gauge) (f : Site n → ℝ) :
    (∑ e:Primary n G,f e.1.1) =
      Fintype.card (Exterior.TypeFace 1)*(Fintype.card G.ColorIndex:ℝ) * ∑ x:Site n,f x := by
  change (∑ e:(Site n × Exterior.TypeFace 1) × G.ColorIndex,f e.1.1) = _
  simp [Fintype.sum_prod_type,← Finset.mul_sum,mul_assoc]
  ring

theorem primary_radial_price (G : Gauge) {a : ℝ} (ha : 0 < a) (b : Site n) :
    (∑ i:Primary n G,Real.exp (-a*separation b i.1.1)) ≤
      (Fintype.card (Exterior.TypeFace 1)*(Fintype.card G.ColorIndex:ℝ)) *
      ((2*(⌈a⁻¹⌉₊:ℝ)+1)^4 * meter 1) := by
  rw [primary_sum G (fun i=>Real.exp (-a*separation b i))]
  exact mul_le_mul_of_nonneg_left (torus_radial_price ha b) (by positivity)

end YM.Integration.FVA1Physical.Round2.Curvature
