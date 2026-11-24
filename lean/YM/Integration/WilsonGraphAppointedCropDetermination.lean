import YM.GradedFar.Crop

/-! An actual positive vanishing heater distinguishes formal series through their inclusive crops. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCropDetermination

open Filter Finset PowerSeries
open scoped BigOperators Topology

theorem determined {ι : Type*} {l : Filter ι} [NeBot l] (θ : ι → ℝ)
    (positive : ∀ᶠ i in l, 0 < θ i) (vanishes : Tendsto θ l (𝓝 0))
    (A B : PowerSeries ℂ)
    (priced : ∀ p : ℕ, ∃ D : ℝ, ∀ᶠ i in l,
      ‖crop p (θ i) A-crop p (θ i) B‖ ≤ D*|θ i|^(p+1)) : A = B := by
  apply PowerSeries.ext
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    obtain ⟨D,paid⟩ := priced p
    have small : ∀ᶠ i in l, ‖coeff p A-coeff p B‖ ≤ D*θ i := by
      filter_upwards [positive,paid] with i hi fee
      have low : ∑ k ∈ range p, ((θ i : ℝ):ℂ)^k * coeff k (A-B) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [map_sub,ih k (Finset.mem_range.mp hk),sub_self,mul_zero]
      rw [← crop_sub,crop_eq,Finset.sum_range_succ,low,zero_add,map_sub,norm_mul,norm_pow,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos hi,pow_succ] at fee
      apply (mul_le_mul_iff_right₀ (pow_pos hi p)).mp
      calc θ i ^ p * ‖coeff p A-coeff p B‖ ≤ D * (θ i ^ p * θ i) := fee
           _ = θ i ^ p * (D*θ i) := by ring
    have lim : Tendsto (fun i => D*θ i) l (𝓝 0) := by simpa using vanishes.const_mul D
    have zero : ‖coeff p A-coeff p B‖ ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds lim small
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm zero (norm_nonneg _)))

end YM.FVA2.GradedFar.AppointedCropDetermination
end

