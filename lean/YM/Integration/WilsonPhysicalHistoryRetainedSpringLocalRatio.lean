import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalSeries

/-! A single real vacuum polynomial normalizes every tested moment of the
incoming physical state. Its lower bound is uniform in Taylor order. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open OriginalMarkedRowCovariance WilsonHeldRetainedAction OriginalMarkedConditionalAction
open WilsonCoeffUV WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open scoped Classical BigOperators
variable {G:Gauge}

private theorem cost_le {n:ℕ}(pn:0<n):springTaylorCost n≤2:=by
  have one:(1:ℝ)≤n:=by exact_mod_cast pn
  have fac:(1:ℝ)≤n.factorial:=by exact_mod_cast Nat.factorial_pos n
  unfold springTaylorCost
  rw [←div_eq_mul_inv,div_le_iff₀ (mul_pos (by positivity) (by positivity))]
  push_cast
  nlinarith only [one,mul_nonneg (sub_nonneg.mpr fac) (show (0:ℝ)≤n by positivity)]

theorem spring_prior_ratio (R:Run G){m N per r:ℕ}(live:m+1≤N){Z:SeriesA G}{σ C ε:ℝ}
    (ep:0≤ε)(osc:LocalSpringOscillation R m N per r Z σ C ε)
    (S:Support (R.family.side (m+1) per))(ext:Config G (R.family.side (m+1) per))
    (W:Config G (R.family.side m per)):
    let δ:=ε*S.card*(regulatorRun R.family N per (m+1))^2
    let ξ:=OriginalMarkedConditionalAction.patch S ext
    let μ:=reference R N per m S ext W
    let ν:=springLocalPrior R m N per S ext W
    let h:=springLocalChange R m N per r Z σ C S ext
    let L (F:Config G (R.family.side (m+1) per)→ℂ):=read μ (fun u=>maskedSpringWeight R (N:=N) r Z σ C (ξ u)) (fun u=>F (ξ u))
    δ≤1/8 → ∀(n:ℕ),0<n→
      let J:=springMomentSum ν h n 1
      ‖J-1‖≤4*δ ∧ 1/2≤‖J‖ ∧ ∀F:Config G (R.family.side (m+1) per)→ℂ,
      Integrable (fun u=>F (ξ u)) ν →
      ‖L F-springMomentSum ν h n (fun u=>F (ξ u))/J‖≤
        6*(δ^n*springTaylorCost n)*(∫u,‖F (ξ u)‖ ∂ν):=by
  intro δ ξ μ ν h L small n pn J
  have domain:δ≤1:=small.trans (by norm_num)
  have pos:0≤δ:=by dsimp [δ];positivity
  letI:IsProbabilityMeasure ν:=(spring_prior_first R live osc S ext W).1
  let p:ℝ:=∫u,Real.exp (h u) ∂ν
  have series:=(spring_prior_series R live ep osc S ext W).2
  let K:=δ^n*springTaylorCost n
  have pk:‖(p:ℂ)-J‖≤K:=(series n pn domain).1
  have unit:‖(p:ℂ)-springMomentSum ν h 1 1‖≤δ^1*springTaylorCost 1:=(series 1 (by decide) domain).1
  have main:‖(p:ℂ)-1‖≤2*δ:=by simpa [springMomentSum,springTaylorCost,mul_comm] using unit
  have power:δ^n≤δ:=by
    obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero pn.ne'
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ pos domain) pos).trans_eq (one_mul _)
  have Ksmall:K≤δ*2:=mul_le_mul power (cost_le pn) (by unfold springTaylorCost;positivity) pos
  have dist:‖J-1‖≤4*δ:=by
    calc ‖J-1‖≤‖J-(p:ℂ)‖+‖(p:ℂ)-1‖:=norm_sub_le_norm_sub_add_norm_sub _ _ _
         _≤K+2*δ:=by rw [norm_sub_rev J];exact add_le_add pk main
         _≤4*δ:=by linarith only [Ksmall]
  have half:1/2≤‖J‖:=by
    have one:=norm_sub_le_norm_sub_add_norm_sub (1:ℂ) J 0
    rw [sub_zero,sub_zero,norm_one,norm_sub_rev (1:ℂ)] at one
    linarith only [one,dist,small]
  refine ⟨dist,half,?_⟩
  intro F act
  let M:=∫u,‖F (ξ u)‖ ∂ν
  let A:=springMomentSum ν h n (fun u=>F (ξ u))
  have native:‖J*L F-A‖≤3*K*M:=((series n pn domain).2 F act).2
  have jp:0<‖J‖:=lt_of_lt_of_le (by norm_num) half
  have j0:J≠0:=norm_pos_iff.mp jp
  have M0:0≤M:=integral_nonneg fun _=>norm_nonneg _
  have K0:0≤K:=by dsimp [K,springTaylorCost];positivity
  calc ‖L F-A/J‖=‖(J*L F-A)/J‖:=by congr 1;field_simp
       _=‖J*L F-A‖/‖J‖:=norm_div ..
       _≤6*K*M:=by
         apply (div_le_iff₀ jp).mpr
         calc ‖J*L F-A‖≤3*K*M:=native
              _=(6*K*M)*(1/2):=by ring
              _≤_:=mul_le_mul_of_nonneg_left half (by positivity)

end YM.Integration.OriginalMarkedRunAction
