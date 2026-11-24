import YM.Comparison.RG02.Thermal.Wick
import YM.Integration.WilsonThermometerAffineVertices

/-! The first two graded integrands of a finite marked block, before any
integration. The cubic contains the whole joint action, while the
differentiated marked exponential includes every incoming occupied mode. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerVertexVariation
open Finset Marker Multi Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Assembly Comparison.RG02.Cumulants PertExtension.Series
open scoped Classical BigOperators
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (l : Hot R→ℕ) (F : Hot R→E→ℂ) (f : E→ℝ)

def vertex (x : E) (n : ℕ) := lit R (fun h => jet (F h) (l h+n) x)

def variation (a b : Poly R) : Poly R :=
  ∑ i∈range (Fintype.card V+1), (i.factorial:ℂ)⁻¹ • (i • (a^(i-1)*b))

omit [Fintype V] in
private theorem product_one (a b : PTable R) :
    PowerSeries.coeff 1 (a*b) = PowerSeries.coeff 0 a*PowerSeries.coeff 1 b+
      PowerSeries.coeff 1 a*PowerSeries.coeff 0 b := by
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

omit [Fintype V] in
private theorem power_one (a : PTable R) (i : ℕ) :
    PowerSeries.coeff 1 (a^i)=i • ((PowerSeries.coeff 0 a)^(i-1)*PowerSeries.coeff 1 a) := by
  induction i with
  | zero => simp [PowerSeries.coeff_one]
  | succ i ih =>
    rw [pow_succ,product_one,ih]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply,map_pow,Nat.succ_sub_one]
    cases i with
    | zero => simp
    | succ n =>
      simp only [Nat.succ_sub_one,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,pow_succ]
      ring

private theorem marked_zero (a : PTable R) :
    PowerSeries.coeff 0 (markExp a)=(PowerSeries.coeff 0 a).pass := by
  unfold markExp Poly.pass
  simp only [map_sum,PowerSeries.coeff_smul,PowerSeries.coeff_zero_eq_constantCoeff_apply,map_pow]

private theorem marked_one (a : PTable R) :
    PowerSeries.coeff 1 (markExp a)=variation (PowerSeries.coeff 0 a) (PowerSeries.coeff 1 a) := by
  simp only [markExp,variation,map_sum,PowerSeries.coeff_smul,power_one]

omit [Fintype V] [FiniteDimensional ℝ E] in
private theorem source (x:E) (n:ℕ) : PowerSeries.coeff n (curve l F x)=vertex l F x n := by
  simp only [curve,vertex,markLetter,PowerSeries.coeff_mk]

omit [FiniteDimensional ℝ E] in
private theorem quiet_zero (x:E) : Radial.expsum (Radial.layers f) 0 0 x=1 := by
  norm_num [Radial.expsum,Zone.TaylorPow,Finset.sum_range_succ]

omit [FiniteDimensional ℝ E] in
private theorem quiet_one (x:E) : Radial.expsum (Radial.layers f) 1 1 x = -jet f 3 x := by
  norm_num only [Radial.expsum,Radial.layers,Finset.sum_range_succ, Finset.sum_range_zero,
    Zone.TaylorPow,Zone.mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,if_true,if_false,
    zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero,Nat.factorial, ← jet_eq,
    Nat.reduceSub,Nat.reduceAdd,neg_add_cancel]

omit [FiniteDimensional ℝ E] in
theorem leading (x : E) : PowerSeries.coeff 0 (expansions l F f x) = (vertex l F x 0).pass := by
  unfold expansions
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,map_mul,←PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ←PowerSeries.coeff_zero_eq_constantCoeff_apply,realCoeff,quiet_zero,Complex.ofReal_one,map_one,one_mul,
    marked_zero,source]

omit [FiniteDimensional ℝ E] in
theorem first (x : E) : PowerSeries.coeff 1 (expansions l F f x) =
    variation (vertex l F x 0) (vertex l F x 1) +
      Poly.bead R (-(↑(jet f 3 x : ℝ) : ℂ)) * (vertex l F x 0).pass := by
  rw [expansions,product_one,realCoeff,realCoeff,quiet_zero,quiet_one,Complex.ofReal_one,
    Complex.ofReal_neg,map_one,one_mul,marked_one,marked_zero,source,source]

end YM.Integration.WilsonThermometerVertexVariation
