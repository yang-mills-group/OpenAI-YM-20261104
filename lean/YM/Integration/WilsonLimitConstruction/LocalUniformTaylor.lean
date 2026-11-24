import YM.Extra.WILSON_STARTUP.Taylor

/-! Uniform remainder estimates for the original real Fréchet Taylor polynomial
in a compact set of external parameters. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.LocalUniformTaylor

open Function Filter Metric WilsonStartup
open scoped ContDiff BigOperators
private theorem polynomial_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (d : ℕ) (a : E) :
    iteratedFDeriv ℝ (d+1) (Work.G05.blockTaylor d f) a = 0 := by
  have term (j : ℕ) (A : Tensor.T E ℝ j) : ∀ k, j < k →
      iteratedFDeriv ℝ k (Tensor.diagonal A) = 0 := by
    have hj : iteratedFDeriv ℝ j (Tensor.diagonal A) =
        fun _ => iteratedFDeriv ℝ j (Tensor.diagonal A) 0 := by
      funext y
      ext1 v
      exact (A.iteratedFDeriv_comp_diagonal y v).trans (A.iteratedFDeriv_comp_diagonal 0 v).symm
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      funext y
      rw [iteratedFDeriv_succ_eq_comp_left,hj]
      simp
      ext1 v
      rfl
    | succ k _ ih =>
      funext y
      rw [iteratedFDeriv_succ_eq_comp_left,ih]
      simp
      ext1 v
      rfl
  unfold Work.G05.blockTaylor
  rw [iteratedFDeriv_sum_apply]
  · exact Finset.sum_eq_zero fun i hi => congr_fun
      (term i (Tensor.coeff f i 0) (d+1) (Finset.mem_range.mp hi)) a
  · exact fun _ _ => (Tensor.diag_smooth ..).contDiffAt

theorem purchase {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Set H) (hK : IsCompact K) (f : H → E → ℝ) (hs : ContDiff ℝ ω (uncurry f))
    (d : ℕ) : ∃ C > 0, ∀ u ∈ K, ∀ j ≤ d+1, ∀ x : E, ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ j (f u - Work.G05.blockTaylor d (f u)) x‖ ≤ C * ‖x‖^(d+1-j) := by
  haveI := FiniteDimensional.proper ℝ E
  let F (p : H × E) := ‖iteratedFDeriv ℝ (d+1) (f p.1) p.2‖
  have hF : Continuous F := (contDiff_partial f hs (d+1)).continuous.norm
  obtain ⟨c,hc⟩ := (hK.prod (isCompact_closedBall (0:E) 1)).bddAbove_image hF.continuousOn
  let C := max 1 c
  have hC : 0 < C := one_pos.trans_le (le_max_left ..)
  refine ⟨C,hC,fun u hu => ?_⟩
  have hf : ContDiff ℝ ω (f u) := hs.comp (f := fun x : E => (u,x))
    (contDiff_const.prodMk contDiff_id)
  have hr : ContDiff ℝ ω (f u - Work.G05.blockTaylor d (f u)) :=
    hf.sub (Work.G05.blockTaylor_contDiff ..)
  have hh (x : E) (hx : ‖x‖ ≤ 1) : ‖iteratedFDeriv ℝ (d+1) (f u - Work.G05.blockTaylor d (f u)) x‖ ≤ C := by
    rw [iteratedFDeriv_sub_apply (hf.contDiffAt.of_le le_top)
      (Work.G05.blockTaylor_contDiff .. |>.contDiffAt),polynomial_top,sub_zero]
    have hin : (u,x) ∈ K ×ˢ Metric.closedBall (0 : E) 1 := ⟨hu,mem_closedBall_zero_iff.mpr hx⟩
    have hout : F (u,x) ≤ c := hc ⟨(u,x),hin,rfl⟩
    exact hout.trans (le_max_right 1 c)
  exact (flat_sub_taylor (f u) d (hf.contDiffAt.of_le le_top)).bound hr hh hC.le

end YM.Integration.WilsonLimitConstruction.LocalUniformTaylor
end
