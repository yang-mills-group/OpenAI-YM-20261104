import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalOscillation
import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalMoment

/-! The first moment is taken under the actual earlier conditional, including
the old constrained gas. Both estimates hold for the same correlated test. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank OriginalMarkedConditionalAction
open OriginalMarkedRowCovariance WilsonHeldRetainedAction
open scoped Classical BigOperators
variable {G:Gauge}

def springLocalPrior (R:Run G)(m N per:ℕ)(S:Support (R.family.side (m+1) per))
    (ext:Config G (R.family.side (m+1) per))(W:Config G (R.family.side m per)):
    Measure (Config G (R.family.side (m+1) per)):=
  SignedWeightedMoment.normalized (reference R N per m S ext W)
    (fun u=>(R.family.path.rep N per (m+1)).eval (OriginalMarkedConditionalAction.patch S ext u))

def springLocalChange (R:Run G)(m N per r:ℕ)(Z:SeriesA G)(σ C:ℝ)(S:Support (R.family.side (m+1) per))
    (ext:Config G (R.family.side (m+1) per))(u:Config G (R.family.side (m+1) per)):ℝ:=
  maskedSpringScore R N per (m+1) r Z σ C (OriginalMarkedConditionalAction.patch S ext u)-
    maskedSpringScore R N per (m+1) r Z σ C ext

theorem spring_prior_bounds (R:Run G){m N per r:ℕ}{Z:SeriesA G}{σ C ε:ℝ}
    (osc:LocalSpringOscillation R m N per r Z σ C ε)
    (S:Support (R.family.side (m+1) per))(ext:Config G (R.family.side (m+1) per)):
    let δ:=ε*S.card*(regulatorRun R.family N per (m+1))^2
    let h:=springLocalChange R m N per r Z σ C S ext
    Measurable h ∧ ∀u,|h u|≤δ/(2*Real.exp 2):=by
  intro δ h
  have meas:=osc.1
  refine ⟨(meas.comp (measurable_patch S ext)).sub measurable_const,?_⟩
  intro u
  apply (le_div_iff₀ (by positivity)).mpr
  exact (mul_comm ..).trans_le (osc.2 S _ _ (outside S ext u))

theorem spring_prior_first (R:Run G){m N per r:ℕ}(live:m+1≤N){Z:SeriesA G}{σ C ε:ℝ}
    (osc:LocalSpringOscillation R m N per r Z σ C ε)
    (S:Support (R.family.side (m+1) per))(ext:Config G (R.family.side (m+1) per))
    (W:Config G (R.family.side m per)):
    let δ:=ε*S.card*(regulatorRun R.family N per (m+1))^2
    let ξ:=OriginalMarkedConditionalAction.patch S ext
    let μ:=reference R N per m S ext W
    let ν:=springLocalPrior R m N per S ext W
    let E:=reading R N per m S ext W (R.family.path.rep N per (m+1))
    let L (F:Config G (R.family.side (m+1) per)→ℂ):=read μ (fun u=>maskedSpringWeight R (N:=N) r Z σ C (ξ u)) (fun u=>F (ξ u))
    IsProbabilityMeasure ν ∧ ∀F:Config G (R.family.side (m+1) per)→ℂ,Integrable (fun u=>F (ξ u)) ν →
      let M:=∫u,‖F (ξ u)‖ ∂ν
      ‖L F-E F‖≤Real.exp δ*δ*M ∧ (δ≤1→‖L F-E F‖≤δ*M):=by
  intro δ ξ μ ν E L
  letI:IsProbabilityMeasure μ:=probability R N per m S ext W
  let a:=δ/(2*Real.exp 2)
  have bound:∀u,|springLocalChange R m N per r Z σ C S ext u|≤a:=(spring_prior_bounds R osc S ext).2
  have ha:0≤a:=(abs_nonneg _).trans (bound ext)
  have factor:2*Real.exp 2*a=δ:=by unfold a;field_simp
  have scaled:2*a≤δ:=by rw [←factor];nlinarith only [mul_le_mul_of_nonneg_right (Real.one_le_exp (by norm_num : (0:ℝ)≤2)) ha]
  obtain ⟨prob,price⟩:=spring_physical_first R live r Z σ C μ ξ (measurable_patch S ext) ext osc.1 a bound
  refine ⟨prob,?_⟩
  intro F acct M
  have m0:0≤M:=integral_nonneg (fun _=>norm_nonneg _)
  have ticket:=price (fun u=>F (ξ u)) acct
  constructor
  · apply ticket.trans (mul_le_mul_of_nonneg_right _ m0)
    calc 2*Real.exp (2*a)*a=Real.exp (2*a)*(2*a):=by ring
         _≤Real.exp δ*δ:=mul_le_mul (Real.exp_le_exp.mpr scaled) scaled (by positivity) (Real.exp_pos _).le
  · intro small
    apply ticket.trans (mul_le_mul_of_nonneg_right _ m0)
    rw [←factor]
    have x:2*a≤2:=by linarith
    gcongr

end YM.Integration.OriginalMarkedRunAction
