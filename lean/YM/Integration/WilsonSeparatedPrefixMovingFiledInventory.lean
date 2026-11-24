import YM.Integration.WilsonSeparatedPrefixMovingCorrectedSum

/-! Restore the initially submitted coefficient inventory on the signed full row
and the subtraction rows before estimating any source coefficient. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingFiledInventory
open PowerSeries
open WilsonSeparatedPrefixMovingCorrectedSum (sign)
open scoped BigOperators Classical
variable {I:Type*}[Fintype I]
local notation "Film" => PowerSeries ℂ
local notation "into" => PowerSeries.map Complex.ofRealHom

def read (c:I → Film)(W:Option I → PowerSeries ℝ):Film:=
  into (W none)-∑i,c i*into (W (some i))

theorem lanes (c:I → Film)(W:Option I → PowerSeries ℝ):
    read c W=∑s,sign c s*into (W s):=by
  rw [Fintype.sum_option];simp only [read,sign,one_mul,neg_mul,Finset.sum_neg_distrib];abel

theorem coupled {A:Option I → Type*}[∀s,Fintype (A s)](c:I → Film)(U K:Option I → PowerSeries ℝ)
    (p Δ:∀s,A s → PowerSeries ℝ)(filed:∀s,U s-K s=∑a,p s a*Δ s a):
    read c U-read c K=∑s,∑a,(sign c s*into (p s a))*into (Δ s a):=by
  rw [lanes,lanes,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl;intro s _
  rw [←mul_sub,←map_sub,filed,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro a _;rw [map_mul,mul_assoc]

theorem price {A:Option I → Type*}[∀s,Fintype (A s)](c:I → Film)(U K:Option I → PowerSeries ℝ)
    (p Δ:∀s,A s → PowerSeries ℝ)(filed:∀s,U s-K s=∑a,p s a*Δ s a)
    (e:ℕ)(bill:∀s,A s → ℝ)(paid:∀s a j,j≤e → ‖coeff j (Δ s a)‖ ≤ bill s a)(q:ℕ)(hq:q≤e):
    ‖coeff q (read c U-read c K)‖ ≤
      ∑s,∑a,∑uv∈Finset.HasAntidiagonal.antidiagonal q,‖coeff uv.1 (sign c s*into (p s a))‖*bill s a:=by
  rw [coupled c U K p Δ filed,map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro s _;rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro a _;rw [coeff_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro uv huv
  have eq:=Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  have wage:=paid s a uv.2 (by omega)
  rw [norm_mul,PowerSeries.coeff_map]
  change ‖coeff uv.1 (sign c s*into (p s a))‖*‖((coeff uv.2 (Δ s a):ℝ):ℂ)‖≤_
  rw [Complex.norm_real]
  exact mul_le_mul_of_nonneg_left wage (norm_nonneg _)

end YM.Integration.WilsonSeparatedPrefixMovingFiledInventory
end
