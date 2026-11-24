import YM.Integration.WilsonRootedPosteriorFiledTangent

/-! Uniform first-order covariance on every bounded measurable reading on the one original earlier fibre. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPosteriorFiledPrices
open Filter Function Finset Lattice RG Wilson Stationary MeasureTheory OPE.Therm
open RG.Shoot Supply Input Precision Marker Multi Exterior Tree Pressure Pressure.Testing
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonLimitConstruction Pert.Asymptotics OriginalMarkedRunAction
open Progress.DirectedRecipe OriginalMarkedRowCovariance WilsonHeldRetainedAction OriginalMarkedConditionalAction
open WilsonRootedPosteriorObserved (slot)
open WilsonRootedPosteriorComparison (value)
open WilsonRootedPosteriorLocalTangent (linear)
open scoped Topology BigOperators Classical
variable {G:Gauge}

theorem bought (R:Run G){m N per r:ℕ}(live:m+1≤N){Z:SeriesA G}{σ C ε:ℝ}(ep:0≤ε)
    (readable:LocalSpringRead R m N per r Z σ C ε)(osc:LocalSpringOscillation R m N per r Z σ C ε)
    (S:Support (R.family.side (m+1) per))(ext:Config G (R.family.side (m+1) per))(W:Config G (R.family.side m per)):
    let δ:=ε*S.card*(regulatorRun R.family N per (m+1))^2
    let ξ:=OriginalMarkedConditionalAction.patch S ext
    let μ:=reference R N per m S ext W
    let ν:=springLocalPrior R m N per S ext W
    let h:=springLocalChange R m N per r Z σ C S ext
    let E:=reading R N per m S ext W (R.family.path.rep N per (m+1))
    let L (u:Config G (R.family.side (m+1) per)→ℂ):=read μ (fun x=>maskedSpringWeight R (N:=N) r Z σ C (ξ x)) (fun x=>u (ξ x))
    let cov (u:Config G (R.family.side (m+1) per)→ℂ):=(∫x,(h x:ℂ)*u (ξ x) ∂ν)-(∫x,(h x:ℂ) ∂ν)*E u
    δ≤1→WilsonRootedPosteriorLocalTangent.Bought E L cov δ (13/4):=by
  intro δ ξ μ ν h E L cov small
  obtain ⟨_,_,measure⟩:=readable S ext W
  have earned:=spring_prior_first R live osc S ext W
  letI:IsProbabilityMeasure ν:=earned.1
  intro z hm B bp cap
  have localEnv:Envelope (fun U=>z (ξ U)):=⟨hm.comp (measurable_patch S ext),B,fun U=>cap _⟩
  have safe:=localEnv.integrableC ν
  have bound:(∫U,‖z (ξ U)‖ ∂ν)≤B:=by
    simpa only [integral_const,probReal_univ,one_smul] using
      (integral_mono safe.norm (integrable_const B) (fun U=>cap (ξ U)))
  obtain ⟨ex,ey,first⟩:=measure z B cap
  refine ⟨⟨bp,ex,ey,?_⟩,?_⟩
  · simpa only [one_mul,norm_sub_rev (E z) (L z)] using first hm
  · have certified:=spring_prior_covariance R live ep osc S ext W small z safe
    exact certified.trans (mul_le_mul_of_nonneg_left bound (mul_nonneg (by norm_num) (sq_nonneg δ)))
end YM.Integration.WilsonRootedPosteriorFiledPrices
