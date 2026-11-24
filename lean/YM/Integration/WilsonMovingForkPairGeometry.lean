import YM.Integration.WilsonMovingForkSampleGeometry

/-! The two-position output panel remains admissible on its own signed
support even when the near test has empty support. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkPairGeometry
open Set RG17
open scoped Classical Topology

theorem original (φ:Test 2):
    ∃M:ℝ,0<M ∧ ∃η:ℝ,0<η ∧ ∀r t:ℝ,0<r → r≤t → ∀z∈tsupport φ,
      (∀i,‖r • (((t/r) • z) i)‖≤M*t) ∧
      (∀i k,i≠k → η≤dist (((t/r) • z) i) (((t/r) • z) k)):=by
  obtain ⟨M,η,mp,ep,room⟩:=RG17.roomCosts φ.hasCompactSupport φ.tsupport_subset
  refine ⟨M+1,by linarith,η,ep,?_⟩
  intro r t rp rt z hz
  have tp:=rp.trans_le rt
  have large:1≤t/r:=(one_le_div rp).mpr rt
  have cancel:r*(t/r)=t:=by field_simp
  refine ⟨?_,?_⟩
  · intro i;change ‖r • ((t/r) • z i)‖≤_
    rw [smul_smul,cancel,norm_smul_of_nonneg tp.le,mul_comm (M+1) t]
    exact mul_le_mul_of_nonneg_left ((show ‖z i‖≤M by simpa [posed] using (room 1 one_pos z hz).span i).trans (by linarith)) tp.le
  · intro i k ne;change η≤dist ((t/r) • z i) ((t/r) • z k)
    rw [dist_eq_norm,←smul_sub,norm_smul_of_nonneg (div_pos tp rp).le,←dist_eq_norm]
    exact (show η≤dist (z i) (z k) by simpa [posed,dist_eq_norm] using (room 1 one_pos z hz).spaced i k ne).trans
      (le_mul_of_one_le_left dist_nonneg large)

end YM.Integration.WilsonMovingForkPairGeometry
end
