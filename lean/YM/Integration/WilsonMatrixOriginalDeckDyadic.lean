import YM.Integration.WilsonMatrixOriginalDeckOutdoor

/-! A finite physical radius path for the signed full-height test. Each successive
radius has ratio at most two, including the final partial interval. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckDyadic
open Filter Set
open scoped Topology

def radius (s t:ℝ) (i:ℕ) : ℝ := min t (s*2^i)

theorem bought {s t:ℝ} (hs:0<s) (hst:s≤t) :
    ∃n:ℕ,radius s t 0=s ∧ radius s t n=t ∧
      (∀i,s≤radius s t i ∧ radius s t i≤t ∧ radius s t i≤radius s t (i+1) ∧ radius s t (i+1)≤2*radius s t i) ∧
      (n:ℝ)≤Real.log (t/s)/Real.log 2+1 := by
  have h2 : 0<Real.log 2:=Real.log_pos (by norm_num)
  have grows:∃j:ℕ,t≤ s*(2:ℝ)^j := by
    obtain ⟨j,hj⟩:=pow_unbounded_of_one_lt (t/s) (by norm_num : 1<(2:ℝ))
    exact ⟨j,by simpa only [mul_comm] using ((div_lt_iff₀ hs).mp hj).le⟩
  let n:=Nat.find grows
  refine ⟨n,by simpa only [radius,pow_zero,mul_one] using min_eq_right hst,
    min_eq_left (Nat.find_spec grows),?_,?_⟩
  · intro i
    have power : 1≤(2:ℝ)^i:=one_le_pow₀ (by norm_num)
    have increasing : s*(2:ℝ)^i ≤ s*2^(i+1):=by rw [pow_succ]; nlinarith [mul_pos hs (by positivity : 0<(2:ℝ)^i)]
    have lower : s≤ s*2^i:=by simpa only [mul_one] using mul_le_mul_of_nonneg_left power hs.le
    refine ⟨le_min hst lower,min_le_left ..,min_le_min_left _ increasing,?_⟩
    unfold radius
    by_cases fits:s*2^i≤t
    · rw [min_eq_right fits]; exact (min_le_right _ _).trans_eq (by rw [pow_succ];ring)
    · rw [min_eq_left (le_of_not_ge fits)]; exact (min_le_left _ _).trans (by linarith)
  · have ratio : 1≤t/s:=(one_le_div hs).mpr hst
    have logpos:=Real.log_nonneg ratio
    cases eqn:n with
    | zero =>
      simp only [Nat.cast_zero]
      linarith [div_nonneg logpos h2.le]
    | succ j =>
      have short : j<n:=by omega
      have before : (2:ℝ)^j<t/s:=(lt_div_iff₀ hs).mpr (by simpa only [mul_comm] using lt_of_not_ge (Nat.find_min grows short))
      have price:=Real.log_lt_log (by positivity) before
      rw [Real.log_pow] at price
      have hj: (j:ℝ)<Real.log (t/s)/Real.log 2:=(lt_div_iff₀ h2).mpr price
      push_cast
      linarith

end YM.Integration.WilsonMatrixOriginalDeckDyadic
