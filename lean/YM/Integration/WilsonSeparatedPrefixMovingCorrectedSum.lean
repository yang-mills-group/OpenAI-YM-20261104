import YM.Integration.WilsonMovingForkPreparedReportedCells

/-! Exact common-clock difference of the full row and its fitted rows, including
every lower feed of each signed coefficient. The exterior purse is shared. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingCorrectedSum
open PowerSeries
open scoped Classical BigOperators
variable {I A:Type*}[Fintype I][Fintype A]
local notation "Film" => PowerSeries ℂ
local notation "into" => PowerSeries.map Complex.ofRealHom

def sign (c:I→Film):Option I→Film
  | none => 1
  | some i => -c i

def measured (exterior:A→Film)(c:I→Film)(T:Option I→A→PowerSeries ℝ):Film:=
  ∑a,∑v,(exterior a*sign c v)*into (T v a)

theorem contrast (exterior:A→Film)(c:I→Film)(T:Option I→A→PowerSeries ℝ):
    measured exterior c T=∑a,exterior a*(into (T none a)-∑i,c i*into (T (some i) a)):=by
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_option]
  simp only [sign,mul_one,mul_neg,neg_mul,Finset.sum_neg_distrib]
  rw [mul_sub,Finset.mul_sum];simp only [mul_assoc];abel

theorem price (exterior:A→Film)(c:I→Film)(U V:Option I→A→PowerSeries ℝ)(B:Option I→A→ℝ)
    (e:ℕ)(income:∀v a j,j≤e→‖coeff j (U v a-V v a)‖≤B v a)(q:ℕ)(hq:q≤e):
    ‖coeff q (measured exterior c U-measured exterior c V)‖≤
      ∑a,∑v,∑p∈Finset.HasAntidiagonal.antidiagonal q,‖coeff p.1 (exterior a*sign c v)‖*B v a:=by
  have diff:measured exterior c U-measured exterior c V=
      ∑a,∑v,(exterior a*sign c v)*into (U v a-V v a):=by
    unfold measured;rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intro a _
    rw [←Finset.sum_sub_distrib];apply Finset.sum_congr rfl;intro v _
    rw [map_sub,mul_sub]
  rw [diff,map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro a _;rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro v _;rw [coeff_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro p hp
  have pay:=income v a p.2 (by have hx:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp;omega)
  rw [norm_mul,PowerSeries.coeff_map]
  change ‖coeff p.1 (exterior a*sign c v)‖*‖((coeff p.2 (U v a-V v a):ℝ):ℂ)‖≤_
  rw [Complex.norm_real]
  exact mul_le_mul_of_nonneg_left pay (norm_nonneg _)
end YM.Integration.WilsonSeparatedPrefixMovingCorrectedSum
end
