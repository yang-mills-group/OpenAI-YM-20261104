import YM.Integration.WilsonSeparatedPrefixMovingUnformedSector

/-! Truncate a signed normalized scalar after it has been evaluated on its
fixed physical outer direction at each retained order. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingHighGrades
open Finset
open scoped BigOperators

def above (J e:ℕ)(g:ℝ)(f:ℕ→ℝ):ℝ:=∑q∈(range (e+1)).filter (fun q=>J<q),g^q*f q

theorem original (J e h:ℕ)(g T fare:ℝ)(f:ℕ→ℝ)(pos:0 ≤ g)(scale:g ≤ 1)(outside:0<T)
    (wage:0 ≤ fare)(priced:∀q,J<q→q ≤ e→‖f q‖ ≤ (T^h)⁻¹*fare):
    ‖above J e g f‖ ≤ (e+1:ℕ)*(g^(J+1)*((T^h)⁻¹*fare)):=by
  have unit:0 ≤ (T^h)⁻¹*fare:=by positivity
  have term (q:ℕ)(invoiced:q∈(range (e+1)).filter (fun q=>J<q)):
      ‖g^q*f q‖ ≤ g^(J+1)*((T^h)⁻¹*fare):=by
    have bounds:=mem_filter.mp invoiced
    have max:=mem_range.mp bounds.1
    rw [norm_mul,Real.norm_of_nonneg (pow_nonneg pos _)]
    exact mul_le_mul (pow_le_pow_of_le_one pos scale (by omega)) (priced q bounds.2 (by omega))
      (norm_nonneg _) (pow_nonneg pos _)
  calc
    _ ≤ ∑q∈(range (e+1)).filter (fun q=>J<q),‖g^q*f q‖:=norm_sum_le ..
    _ ≤ ∑_q∈(range (e+1)).filter (fun q=>J<q),g^(J+1)*((T^h)⁻¹*fare):=sum_le_sum term
    _ ≤ ∑_q∈range (e+1),g^(J+1)*((T^h)⁻¹*fare):=sum_le_sum_of_subset_of_nonneg
      (filter_subset ..) (fun _ _ _=>mul_nonneg (pow_nonneg pos _) unit)
    _=_:=by simp

end YM.Integration.WilsonSeparatedPrefixMovingHighGrades
