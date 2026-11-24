import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalExact
import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalTaylor

/-! A finite physical numerator and vacuum correction on the original local
Wilson law, with every power of the same incoming action discrepancy retained. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open OriginalMarkedRowCovariance WilsonHeldRetainedAction OriginalMarkedConditionalAction
open WilsonCoeffUV WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open scoped Classical BigOperators
variable {G:Gauge}

theorem spring_prior_series (R:Run G){m N per r:ℕ}(live:m+1≤N){Z:SeriesA G}{σ C ε:ℝ}
    (ep:0≤ε)(osc:LocalSpringOscillation R m N per r Z σ C ε)
    (S:Support (R.family.side (m+1) per))(ext:Config G (R.family.side (m+1) per))
    (W:Config G (R.family.side m per)):
    let δ:=ε*S.card*(regulatorRun R.family N per (m+1))^2
    let ξ:=OriginalMarkedConditionalAction.patch S ext
    let μ:=reference R N per m S ext W
    let ν:=springLocalPrior R m N per S ext W
    let h:=springLocalChange R m N per r Z σ C S ext
    let p:=∫u,Real.exp (h u) ∂ν
    let L (F:Config G (R.family.side (m+1) per)→ℂ):=read μ (fun u=>maskedSpringWeight R (N:=N) r Z σ C (ξ u)) (fun u=>F (ξ u))
    0<p ∧ ∀(n:ℕ),0<n→δ≤1→
      let K:=δ^n*springTaylorCost n
      ‖(p:ℂ)-springMomentSum ν h n 1‖≤K ∧
      ∀F:Config G (R.family.side (m+1) per)→ℂ,Integrable (fun u=>F (ξ u)) ν →
      let M:=∫u,‖F (ξ u)‖ ∂ν
      let num:=springMomentSum ν h n (fun u=>F (ξ u))
      ‖(p:ℂ)*L F-num‖≤K*M ∧ ‖springMomentSum ν h n 1*L F-num‖≤3*K*M:=by
  intro δ ξ μ ν h p L
  have controls:=spring_prior_first R live osc S ext W
  letI:IsProbabilityMeasure ν:=controls.1
  have exactLaw:=spring_prior_exact R live osc S ext W
  have recorded:=spring_prior_bounds R osc S ext
  have zero:0≤δ:=by dsimp [δ];positivity
  have denom:1≤2*Real.exp 2:=by linarith only [Real.one_le_exp (by norm_num : (0:ℝ)≤2)]
  have bound (u):|h u|≤δ:=(recorded.2 u).trans (div_le_self zero denom)
  refine ⟨exactLaw.1,?_⟩
  intro n pn small K
  have kn:0≤K:=by dsimp [K,springTaylorCost];positivity
  have pure:‖(p:ℂ)-springMomentSum ν h n 1‖≤K:=by
    simpa only [p,K,Pi.one_apply,mul_one,norm_one,integral_const,probReal_univ,one_smul,integral_complex_ofReal] using spring_moment_sum ν h recorded.1 bound small n pn (1:Config G (R.family.side (m+1) per)→ℂ)
      (integrable_const (μ:=ν) 1)
  refine ⟨pure,?_⟩
  intro F actual M num
  have native:‖(p:ℂ)*L F-num‖≤K*M:=by
    rw [(exactLaw.2 F).2]
    exact spring_moment_sum ν h recorded.1 bound small n pn _ actual
  have pos:0≤M:=integral_nonneg (fun _=>norm_nonneg _)
  let E:=reading R N per m S ext W (R.family.path.rep N per (m+1)) F
  have obs:‖E‖≤M:=by dsimp only [E];rw [(exactLaw.2 F).1];exact norm_integral_le_integral_norm _
  have cmp:‖L F-E‖≤δ*M:=(controls.2 F actual).2 small
  have total:‖L F‖≤2*M:=by
    calc ‖L F‖=‖(L F-E)+E‖:=by rw [sub_add_cancel]
         _≤‖L F-E‖+‖E‖:=norm_add_le _ _
         _≤δ*M+M:=add_le_add cmp obs
         _≤2*M:=by nlinarith only [mul_le_mul_of_nonneg_right small pos]
  let J:=springMomentSum ν h n 1
  have rev:‖J-(p:ℂ)‖≤K:=by rw [norm_sub_rev];exact pure
  refine ⟨native,?_⟩
  calc ‖J*L F-num‖=‖(J-(p:ℂ))*L F+((p:ℂ)*L F-num)‖:=by congr 1;ring
       _≤‖(J-(p:ℂ))*L F‖+‖(p:ℂ)*L F-num‖:=norm_add_le _ _
       _≤K*(2*M)+K*M:=by rw [norm_mul];exact add_le_add (mul_le_mul rev total (norm_nonneg _) kn) native
       _=3*K*M:=by ring

end YM.Integration.OriginalMarkedRunAction
