import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalSeries

/-! The first connected correction, in the true conditional law of the old
physical pupil, including its full compatible gas and both normalizations. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open OriginalMarkedRowCovariance WilsonHeldRetainedAction OriginalMarkedConditionalAction
open WilsonCoeffUV WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open scoped Classical BigOperators
variable {G:Gauge}

private theorem moment_two {X:Type*}[MeasurableSpace X](μ:Measure X)(h:X→ℝ)(F:X→ℂ):
    springMomentSum μ h 2 F=(∫u,F u ∂μ)+∫u,(h u:ℂ)*F u ∂μ:=by
  simp [springMomentSum,Finset.sum_range_succ]

theorem spring_prior_covariance (R:Run G){m N per r:ℕ}(live:m+1≤N){Z:SeriesA G}{σ C ε:ℝ}
    (ep:0≤ε)(osc:LocalSpringOscillation R m N per r Z σ C ε)
    (S:Support (R.family.side (m+1) per))(ext:Config G (R.family.side (m+1) per))
    (W:Config G (R.family.side m per)):
    let δ:=ε*S.card*(regulatorRun R.family N per (m+1))^2
    let ξ:=OriginalMarkedConditionalAction.patch S ext
    let μ:=reference R N per m S ext W
    let ν:=springLocalPrior R m N per S ext W
    let h:=springLocalChange R m N per r Z σ C S ext
    let A:=∫u,(h u:ℂ) ∂ν
    δ≤1 → ∀F:Config G (R.family.side (m+1) per)→ℂ,Integrable (fun u=>F (ξ u)) ν →
      let E:=reading R N per m S ext W (R.family.path.rep N per (m+1)) F
      let L:=read μ (fun u=>maskedSpringWeight R (N:=N) r Z σ C (ξ u)) (fun u=>F (ξ u))
      let covariance:=(∫u,(h u:ℂ)*F (ξ u) ∂ν)-A*E
      ‖L-E-covariance‖≤(13/4 : ℝ)*δ^2*(∫u,‖F (ξ u)‖ ∂ν):=by
  intro δ ξ μ ν h A small F actual E L covariance
  let M:=∫u,‖F (ξ u)‖ ∂ν
  have base:=spring_prior_first R live osc S ext W
  letI:IsProbabilityMeasure ν:=base.1
  have prior:=spring_prior_exact R live osc S ext W
  have series:=((spring_prior_series R live ep osc S ext W).2 2 (by decide) small).2 F actual
  have quiet:springMomentSum ν h 2 1=1+A:=by simp [moment_two,A]
  have mark:springMomentSum ν h 2 (fun u=>F (ξ u))=E+(∫u,(h u:ℂ)*F (ξ u) ∂ν):=by
    rw [moment_two, show E=∫u,F (ξ u) ∂ν from (prior.2 F).1]
  have two:springTaylorCost 2=3/4:=by norm_num [springTaylorCost,Nat.factorial]
  have residual:‖(1+A)*L-(E+(∫u,(h u:ℂ)*F (ξ u) ∂ν))‖≤3*(δ^2*(3/4))*M:=by
    have cash:‖springMomentSum ν h 2 1*L-springMomentSum ν h 2 (fun u=>F (ξ u))‖≤3*(δ^2*springTaylorCost 2)*M:=series.2
    rwa [quiet,mark,two] at cash
  have pos:0≤δ:=by dsimp [δ];positivity
  have denom:1≤2*Real.exp 2:=by linarith only [Real.one_le_exp (by norm_num : (0:ℝ)≤2)]
  have bound (u):‖(h u:ℂ)‖≤δ:=by simpa only [Complex.norm_real,Real.norm_eq_abs] using
        (((spring_prior_bounds R osc S ext).2 u).trans (div_le_self pos denom))
  have mean:‖A‖≤δ:=by simpa only [A,probReal_univ,mul_one] using
        (norm_integral_le_of_norm_le_const (μ:=ν) (C:=δ) (Filter.Eventually.of_forall bound))
  have diff:‖L-E‖≤δ*M:=(base.2 F actual).2 small
  calc ‖L-E-covariance‖=
         ‖((1+A)*L-(E+(∫u,(h u:ℂ)*F (ξ u) ∂ν)))-A*(L-E)‖:=by dsimp only [covariance];congr 1;ring
       _≤‖(1+A)*L-(E+(∫u,(h u:ℂ)*F (ξ u) ∂ν))‖+‖A*(L-E)‖:=norm_sub_le _ _
       _≤3*(δ^2*(3/4))*M+δ*(δ*M):=by rw [norm_mul];exact add_le_add residual (mul_le_mul mean diff (norm_nonneg _) pos)
       _=(13/4 : ℝ)*δ^2*M:=by ring

end YM.Integration.OriginalMarkedRunAction
