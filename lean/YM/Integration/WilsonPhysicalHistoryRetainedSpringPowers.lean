import YM.Integration.WilsonPhysicalHistoryRetainedSpringOrder

/-! The physical inverse temperature costs precisely two powers.  All the
additional powers from the original engineering label remain in the estimate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Comparison.RG02

theorem weighted_power {g p K D : ℝ} (hg : 0<g) (lo : 1/2≤p) (hi : p≤3/2)
    (hk : 0≤K) (hd : 0≤D) (r h : ℕ) :
    |Integral.temperature g*p*(g/Real.sqrt p)^r| *(D*(K*g)^(h+2)) ≤
      2^(r+1)*D*K^(h+2)*g^(r+h) := by
  have hp : 0<p:=by linarith
  have sq:=Real.sq_sqrt hp.le
  have hs : (1/2:ℝ)≤Real.sqrt p:=by nlinarith [Real.sqrt_nonneg p]
  have hc : |g/Real.sqrt p|≤2*g:=by
    rw [abs_of_nonneg (div_nonneg hg.le (Real.sqrt_nonneg _)),div_le_iff₀ (Real.sqrt_pos.2 hp)]
    nlinarith [mul_nonneg hg.le (sub_nonneg.mpr hs)]
  have hb : |Integral.temperature g*p|≤(g^2)⁻¹*2:=by
    unfold Integral.temperature
    rw [abs_of_nonneg (mul_nonneg (by positivity) hp.le)]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc
    _ ≤ (g^2)⁻¹*2*(2*g)^r*(D*(K*g)^(h+2)) := by
      rw [abs_mul,abs_pow]
      exact mul_le_mul_of_nonneg_right (mul_le_mul hb
        (pow_le_pow_left₀ (abs_nonneg _) hc r) (by positivity) (by positivity)) (by positivity)
    _ = _ := by
      rw [mul_pow,mul_pow,pow_add g h 2,pow_add g r h,pow_succ (2:ℝ)]
      field_simp [hg.ne']

end YM.Integration.OriginalMarkedRunAction
