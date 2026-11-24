import YM.TraceExtension.Lamp.Keg

/-! Explicit quantitative Taylor remainder for the actual nonlinear
position-screen read of the independently filed MS polynomial. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOrdinaryPositionTaylor
open Function Filter Set Finset Push.Uniform
open scoped Topology Classical BigOperators ContDiff
variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

private theorem allowance (f : ℝ→Y) (q : ℕ) (smooth : ContDiffAt ℝ ω f 0) :
    ∃ A : ℝ,0≤A ∧ ∃ s : ℝ,0<s ∧ ∀t∈Icc 0 s,Allows q f t A := by
  let bounds (i : Fin (q+1)) := ‖iteratedFDeriv ℝ i.val f 0‖+1
  let A := ∑ i : Fin (q+1),bounds i
  have pos (i : Fin (q+1)) : 0≤bounds i := by dsimp [bounds];positivity
  have individually (i : Fin (q+1)) : ∀ᶠ t : ℝ in 𝓝 0,‖iteratedFDeriv ℝ i.val f t‖<bounds i := by
    have cont : ContinuousAt (iteratedFDeriv ℝ i.val f) 0 :=
      smooth.continuousAt_iteratedFDeriv (by exact_mod_cast le_top)
    exact cont.norm.tendsto.eventually (eventually_lt_nhds (lt_add_one _))
  have smoothNear : ∀ᶠ t : ℝ in 𝓝 0,ContDiffAt ℝ ω f t :=
    smooth.analyticAt.eventually_analyticAt.mono fun _ h=>h.contDiffAt
  have near : ∀ᶠ t : ℝ in 𝓝 0,Allows q f t A := by
    filter_upwards [Filter.eventually_all.mpr individually,smoothNear] with t h ht
    refine ⟨ht,?_⟩
    intro j hj
    let i : Fin (q+1) := ⟨j,Nat.lt_succ_of_le hj⟩
    exact (h i).le.trans (single_le_sum (fun z _=>pos z) (mem_univ i))
  obtain ⟨b,hb,small⟩ := Metric.mem_nhds_iff.mp near
  refine ⟨A,sum_nonneg (fun i _=>pos i),b/2,by positivity,?_⟩
  intro t ht
  apply small
  rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg ht.1]
  linarith [ht.2]

def truncation (f : ℝ→Y) (q : ℕ) (t : ℝ) :=
  ∑ j ∈ range (q+1),t^j • ((j.factorial:ℝ)⁻¹ • iteratedDeriv j f 0)

theorem remainder (f : ℝ→Y) (smooth : ContDiffAt ℝ ω f 0) (q : ℕ) :
    ∃ K : ℝ,0≤K ∧ ∀ᶠ t : ℝ in 𝓝[>]0,‖f t-truncation f q t‖≤K*t^(q+1) := by
  obtain ⟨A,hA,s,hs,bound⟩ := allowance f (q+1) smooth
  refine ⟨A/(q.factorial:ℝ),by positivity,?_⟩
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hs).filter_mono nhdsWithin_le_nhds] with t pos small
  have step := Trace.Lamp.warm f s hs t ⟨le_of_lt pos,small.le⟩ q bound
  calc
    ‖f t-truncation f q t‖ = ‖f t-∑ j ∈ range (q+1),t^j • Trace.Lamp.neap j f 0 1‖ := by
      simp only [truncation,Trace.Lamp.neap,iteratedDeriv_eq_iteratedFDeriv]
    _ ≤ A*t^(q+1)/(q.factorial:ℝ) := step
    _ = _ := by ring

end YM.Integration.WilsonOrdinaryPositionTaylor
end

