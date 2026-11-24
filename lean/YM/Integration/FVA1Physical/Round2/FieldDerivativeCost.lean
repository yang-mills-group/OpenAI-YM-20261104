import YM.Integration.FVA1Physical.Round2.FieldChartOrder
import YM.MSbar.Mosaic.Model

/-! The measured inverse coupling absorbs all sparse chart derivatives for a
fixed word length without charging the size of the lattice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Lattice RG Push.Uniform Push.Local.Kernel MSbar.Midpoint MSbar.Mosaic MSbar.Heath.Stock
open Finset Planned.AtomRegular
open scoped Classical Topology BigOperators

private def chartMultiplier (G : Gauge) (k : ℕ) (a : ℝ) : ℝ :=
  (k.factorial:ℝ)*(∑ j∈range (k+1),polarCost j)*a*(1+composeCost k (account k G).choose 2)^k

private theorem chartMultiplier_nonneg (G : Gauge) (k : ℕ) {a : ℝ} (ha : 0≤a) :
    0 ≤ chartMultiplier G k a := by
  have pay := (account k G).choose_spec.1
  have wages : 0≤∑ j∈range (k+1),polarCost j := sum_nonneg fun j _=>zero_le_one.trans (polar_one j)
  unfold chartMultiplier composeCost
  positivity

private theorem chart_price_factor (G : Gauge) (u : ℝ) (k m : ℕ) (a : ℝ) :
    chartOrderPrice G u k m a=chartMultiplier G k a * responsePrice G u k m 1 := by
  unfold chartOrderPrice chartMultiplier tangentOrderPrice composeCost
  ring

theorem sparse_chart_polynomial (G : Gauge) (u β : ℝ) (k m q : ℕ) {a : ℝ}
    (ha : 0≤a) (hβ : 1≤β) (hm : m≤q) :
    chartOrderPrice G (β*u) k m a ≤ chartOrderPrice G |u| k q a * β^responseDegree k := by
  have price:=sparse_price_polynomial G k m q zero_le_one (abs_nonneg u) hβ
    (show |β*u| ≤ |u| * β by rw [abs_mul,abs_of_nonneg (zero_le_one.trans hβ),mul_comm]) hm
  simp only [chart_price_factor,mul_assoc]
  exact mul_le_mul_of_nonneg_left price (chartMultiplier_nonneg G k ha)

def chartInversePower (k : ℕ) := 2*(max 1 (responseDegree k)+1)

theorem actual_chart_fee {G : Gauge} (A : Issue G) (k m q n : ℕ) {a H : ℝ}
    (ha : 0≤a) (hm : m≤q) (hβ : 1≤A.pre.beta) (rows : H≤A.pre.beta)
    (large : chartOrderPrice G |A.S.kernel.penalty| k q a + ((n+1:ℕ):ℝ) ≤ A.pre.beta) :
    chartOrderPrice G (A.pre.beta*A.S.kernel.penalty) k m a + ((n+1:ℕ):ℝ)*H ≤
      (A.fClock⁻¹)^chartInversePower k := by
  let β:=A.pre.beta
  let d:=max 1 (responseDegree k)
  let C:=chartOrderPrice G |A.S.kernel.penalty| k q a
  have hC : 0≤C := by
    dsimp only [C]
    rw [chart_price_factor]
    exact mul_nonneg (chartMultiplier_nonneg G k ha) (responsePrice_nonnegative G _ k q zero_le_one)
  have left:= (sparse_chart_polynomial G A.S.kernel.penalty β k m q ha hβ hm).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hβ (le_max_right 1 (responseDegree k))) hC)
  have right : H≤β^d := rows.trans (by simpa only [pow_one] using pow_le_pow_right₀ hβ (le_max_left 1 (responseDegree k)))
  apply (add_le_add left (mul_le_mul_of_nonneg_left right (Nat.cast_nonneg (n+1)))).trans
  rw [←add_mul]
  apply (mul_le_mul_of_nonneg_right large (pow_nonneg (zero_le_one.trans hβ) d)).trans_eq
  change β * β^d=((Real.sqrt β)⁻¹)⁻¹ ^ (2*(d+1))
  rw [inv_inv,pow_mul,Real.sq_sqrt (zero_le_one.trans hβ),pow_succ,mul_comm]

end YM.Integration.FVA1Physical.Round2.Curvature
