import YM.Integration.WilsonPositionProgramFiledGaussianPrice

/-! An explicit polynomial envelope for a lower Wilson fluctuation and its zeroth anchored value. -/
noncomputable section
namespace YM.Integration.WilsonPositionProgramGaussianRadialStock
open Function Finset Marker Multi Comparison.RG02
open Next.SectorChange Next.SectorChange.Gaussian Next.Rank Comparison.RG02.Cumulants
open WilsonPositionProgramGaussianRoute
open scoped Classical BigOperators
variable {I:Type}[Fintype I]

def radial (k:ℕ):Normal.poly I:= (2*(1+∑i:I,(MvPolynomial.X i)^2))^k

theorem read (z:I→ℝ)(k:ℕ):
    Cloud.paint z (radial k)=(↑((2*(1+∑i:I,(z i)^2))^k):ℂ) := by
  simp [radial,Cloud.paint]

theorem priced (z:I→ℝ)(k:ℕ):(1+‖z‖)^k ≤ (Cloud.paint z (radial k)).re := by
  have pos:0≤∑i:I,(z i)^2:=sum_nonneg fun i _=>sq_nonneg _
  have norm:‖z‖ ≤ 1+∑i:I,(z i)^2:=by
    apply (pi_norm_le_iff_of_nonneg (by linarith)).2
    intro i
    have entry:(z i)^2≤∑j:I,(z j)^2:=single_le_sum (f:=fun j=>(z j)^2) (fun j _=>sq_nonneg _) (mem_univ i)
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (z i),sq_nonneg (|z i|-1)]
  rw [read,Complex.ofReal_re]
  exact pow_le_pow_left₀ (by positivity) (by linarith) k

variable {V:Type}[DecidableEq V]{R:Census V}

theorem centered (s:R.Mode)(i:Hot R)(delta:Normal.poly I)(a:ℝ)(ha:0≤a)(k:ℕ)
    (price:∀z:I→ℝ,‖Cloud.paint z delta‖ ≤ a*(1+‖z‖)^k)(z:I→ℝ):
    ‖Cloud.paint z (anchored s 0 i delta)‖ ≤ (2*a)*(Cloud.paint z (radial k)).re := by
  have one:1≤(1+‖z‖)^k:=one_le_pow₀ (by linarith [norm_nonneg z])
  have re:=priced z k
  have av:a≤a*(Cloud.paint z (radial k)).re:=by simpa using mul_le_mul_of_nonneg_left (one.trans re) ha
  have pp:‖Cloud.paint z delta‖ ≤ a*(Cloud.paint z (radial k)).re:=
    (price z).trans (mul_le_mul_of_nonneg_left re ha)
  have orig:=price 0
  simp only [norm_zero,add_zero,one_pow,mul_one] at orig
  unfold anchored
  split_ifs
  · linarith [norm_nonneg (Cloud.paint z delta)]
  · rw [map_sub]
    have mapped:Cloud.paint z (MvPolynomial.C (Cloud.paint 0 delta))=Cloud.paint 0 delta:=by simp [Cloud.paint]
    rw [mapped]
    exact (norm_sub_le _ _).trans (by linarith)

end YM.Integration.WilsonPositionProgramGaussianRadialStock
end
