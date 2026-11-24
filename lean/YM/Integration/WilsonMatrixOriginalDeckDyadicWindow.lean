import YM.Integration.WilsonMatrixOriginalDeckDyadic

/-! The genuine funded radius neighborhoods contain a common complete dyadic
path, including its two endpoints, before the cutoff or period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckDyadicWindow
open Filter Set Trace.Pilot WilsonMatrixOriginalDeckDyadic
open scoped Topology

theorem interior {W:Set ℝ} (openW:W∈trail) :
    ∀ᶠt:ℝ in trail,∀s:ℝ,0<s→s≤t→∀i:ℕ,radius s t i∈W := by
  obtain ⟨ε,hε,inside⟩:=Metric.mem_nhdsWithin_iff.mp openW
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0:ℝ) hε)] with t ht
  intro s hs st i
  have hi : 0<radius s t i:=lt_min (hs.trans_le st) (mul_pos hs (by positivity))
  have htr : t<ε:=by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (hs.trans_le st)] using ht
  have close : radius s t i<ε:=(min_le_left t (s*2^i)).trans_lt htr
  refine inside ⟨?_,hi⟩
  simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hi] using close

theorem horizon {W:Set ℝ} (openW:W∈trail) (b:ℕ) :
    ∀ᶠt:ℝ in trail,∀s g K:ℝ,0<s→s≤t→0<g→0<K→ t/s≤K*g^(-(b:ℝ)) →
    ∃n:ℕ,radius s t 0=s ∧ radius s t n=t ∧ (∀i:ℕ,radius s t i∈W) ∧
      (∀i,s≤radius s t i ∧ radius s t i≤t ∧ radius s t i≤radius s t (i+1) ∧ radius s t (i+1)≤2*radius s t i) ∧
      (n:ℝ) ≤ (Real.log K-(b:ℝ)*Real.log g)/Real.log 2+1 := by
  filter_upwards [interior openW] with t fits
  intro s g K hs hst hg hk bound
  obtain ⟨n,first,last,ratios,count⟩:=bought hs hst
  have logBound:=Real.log_le_log (div_pos (hs.trans_le hst) hs) bound
  rw [Real.log_mul hk.ne' (Real.rpow_pos_of_pos hg _).ne',Real.log_rpow hg] at logBound
  refine ⟨n,first,last,fits s hs hst,ratios,count.trans ?_⟩
  have ratio : Real.log (t/s)/Real.log 2≤(Real.log K-(b:ℝ)*Real.log g)/Real.log 2 :=
    div_le_div_of_nonneg_right (by linarith) (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  linarith

end YM.Integration.WilsonMatrixOriginalDeckDyadicWindow
