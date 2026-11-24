import YM.Integration.SignedChartTaylor

/-! One finite-dimensional Taylor price for all values of a compact
background. The perturbation is confined to its submitted direction. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentFrozenTaylor
open Set Metric Finset AnalyticBridge.SectorAffine.Offset
open scoped ContDiff

variable {K E : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem purchased (F : E → ℂ) (hf : ContDiff ℝ ω F) (b : K → E) (hb : Continuous b)
    (p : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ k a (t : ℝ), 0 < t → t*‖a‖<1 →
    ‖F (b k+t•a) - ∑ j ∈ range (p+1),t^j • SignedChartTaylor.jet (fun y => F (b k+y)) a j‖
      ≤ C*(t*‖a‖)^(p+1) := by
  classical
  obtain ⟨r,hr⟩ := isCompact_univ.exists_bound_of_continuousOn hb.continuousOn
  have paid (j : ℕ) : ∃ C : ℝ, ∀ x ∈ closedBall (0:E) (r+1),
      ‖iteratedFDeriv ℝ j F x‖ ≤ C :=
    (isCompact_closedBall (0:E) (r+1)).exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (m:=j) le_top).continuousOn
  choose fee valid using paid
  let c := ∑ j ∈ range (p+2),max (fee j) 0
  have pos : 0 ≤ c := sum_nonneg fun _ _ => le_max_right _ _
  refine ⟨c/(p.factorial:ℝ),div_nonneg pos (by positivity),?_⟩
  intro k a t ht ht'
  have bill (z : E) (hz : ‖z‖<1) : Through (p+1) (fun y => F (b k+y)) z c := by
    refine ⟨(hf.comp (contDiff_const.add contDiff_id)).contDiffAt.of_le le_top,?_⟩
    intro j hj
    rw [iteratedFDeriv_comp_add_left]
    have here : b k+z ∈ closedBall (0:E) (r+1) := by
      rw [mem_closedBall_zero_iff]
      exact (norm_add_le _ _).trans (add_le_add (hr k (mem_univ _)) hz.le)
    exact (valid j _ here).trans ((le_max_left _ _).trans
      (single_le_sum (fun _ _ => le_max_right _ _) (mem_range.mpr (by omega))))
  apply (SignedChartTaylor.window (fun y => F (b k+y)) a p t c ht ht' bill).trans_eq
  ring

end YM.Integration.WilsonCoherentFrozenTaylor
