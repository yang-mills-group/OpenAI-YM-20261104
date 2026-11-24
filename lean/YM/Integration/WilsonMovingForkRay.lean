import YM.Integration.WilsonSeparatedLatticeStencil
import YM.Integration.WilsonMovingForkTubeJets

/-! Signed Lagrange sampling from an actual physical germ at each point of an
axis segment. The factor `c^(m+1)` is the phase-selected lattice spacing in near units. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkRay
open Function Filter Set Metric Contacts.Mat
open scoped Classical Topology BigOperators

private theorem smooth {f:ℝ→ℂ}{t:ℝ}(ha:AnalyticAt ℝ f t)(j:ℕ):AnalyticAt ℝ (iteratedDeriv j f) t:=by
  induction j with
  | zero=>simpa only [iteratedDeriv_zero] using ha
  | succ j ih=>rw [iteratedDeriv_succ];exact ih.deriv

/-- The displayed equality is only required as a germ at each actual node of the
real axis segment. The normalized Wilson posterior never enters a complex point. -/
theorem original {m:ℕ}{H ρ M c:ℝ}(rp:0<ρ)(cp:0<c)(mp:0≤M)(U:Nodes m H)(f:ℝ→ℂ)
    (model:∀t∈Icc 0 H,∃g:ℂ→ℂ,AnalyticOnNhd ℂ g (closedBall 0 ρ) ∧
      (∀z∈closedBall 0 ρ,‖g z‖≤M) ∧
      f=ᶠ[𝓝 t]fun s:ℝ=>g ((c*(s-t):ℝ):ℂ)):
    ‖f 0-∑j,bleed U.v j • f (U.v j)‖ ≤
        ((m+1:ℕ):ℝ)*H^m*((m+1).factorial*M*c^(m+1)/ρ^(m+1)*(H^(m+1)/(m.factorial:ℝ))):=by
  have rate (t:ℝ)(ht:t∈Icc 0 H): AnalyticAt ℝ f t ∧ ∀j:ℕ,
      ‖iteratedDeriv j f t‖≤j.factorial*M*c^j/ρ^j:=by
    obtain ⟨g,analytic,size,same⟩:=model t ht
    let axis(z:ℂ):= (c:ℂ)*(z-(t:ℂ))
    let movie(z:ℂ):=g (axis z)
    have qpos:0<ρ/c:=div_pos rp cp
    have near(z:ℂ)(hz:z∈closedBall (t:ℂ) (ρ/c)):axis z∈closedBall 0 ρ:=by
      rw [mem_closedBall,dist_zero_right,norm_mul,Complex.norm_real,Real.norm_of_nonneg cp.le]
      rw [mem_closedBall,dist_eq_norm] at hz
      simpa only [mul_comm c] using (le_div_iff₀ cp).mp hz
    have hol:AnalyticOnNhd ℂ movie (closedBall (t:ℂ) (ρ/c)):=fun z hz=>(analytic _ (near z hz)).comp (by dsimp only [axis];fun_prop)
    have axisAt:AnalyticAt ℂ movie (t:ℂ):=hol _ (mem_closedBall_self qpos.le)
    have same':f=ᶠ[𝓝 t]fun s:ℝ=>movie s:=by
      simpa only [movie,axis,Complex.ofReal_mul,Complex.ofReal_sub] using same
    have realHol:AnalyticAt ℝ (fun s:ℝ=>movie s) t:=axisAt.restrictScalars.comp (Complex.ofRealCLM.analyticAt _)
    refine ⟨realHol.congr same'.symm,?_⟩
    intro j
    rw [same'.iteratedDeriv_eq j,WilsonSeparatedTubeCauchy.real_jet axisAt j]
    have diff:=hol.differentiableOn
    have bound:=Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j qpos
      (f:=movie) (c:=(t:ℂ)) ⟨diff.mono ball_subset_closedBall,diff.continuousOn.mono closure_ball_subset_closedBall⟩
      (fun z hz=>size _ (near z (sphere_subset_closedBall hz)))
    exact bound.trans_eq (by rw [div_pow];field_simp)
  have W:0≤(m+1).factorial*M*c^(m+1)/ρ^(m+1):=by positivity
  have wages:=WilsonSeparatedLatticeStencil.error U (fun j=>iteratedDeriv j f) _ W
    (fun t ht j _=>by rw [iteratedDeriv_succ];exact (smooth (rate t ht).1 j).differentiableAt.hasDerivAt)
    (fun t ht=>(rate t ht).2 _)
  simpa only [iteratedDeriv_zero] using wages

end YM.Integration.WilsonMovingForkRay
