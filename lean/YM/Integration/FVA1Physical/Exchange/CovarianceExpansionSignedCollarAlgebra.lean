import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Localize a full signed residual to the complement of a paid event.
All products use one measure, the same signed test, and one component. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseDatedReceived
open MeasureTheory Set
open scoped Classical

theorem paid_signed_complement {T:Type*}[MeasurableSpace T]
    (μ:Measure T)(E:Set T)(em:MeasurableSet E)(A H Y:T→ℂ)(ym:MemLp Y 2 μ)
    {τ cost toll:ℝ}(tp:0≤τ)(cp:0≤cost)
    (regular:∀Z:T→ℂ,MemLp Z 2 μ →
      Integrable (fun t=>Z t*(A t-H t)) μ ∧
      τ*‖∫t,Z t*(A t-H t) ∂μ‖≤Real.sqrt (∫t,‖Z t‖^2 ∂μ)*cost)
    (failed:Integrable (fun t=>E.indicator (fun u=>(τ:ℂ)*A u) t *Y t) μ ∧
      ‖∫t,E.indicator (fun u=>(τ:ℂ)*A u) t *Y t ∂μ‖≤Real.sqrt (∫t,‖Y t‖^2 ∂μ)*toll):
    let F:=fun t=>(τ:ℂ)*Y t*(A t-Eᶜ.indicator H t)
    Integrable F μ ∧ ‖∫t,F t ∂μ‖≤Real.sqrt (∫t,‖Y t‖^2 ∂μ)*(cost+toll):=by
  intro F
  let Z:=Eᶜ.indicator Y
  let soft:=fun t=>Z t*(A t-H t)
  let hard:=fun t=>E.indicator (fun u=>(τ:ℂ)*A u) t*Y t
  have zm:MemLp Z 2 μ:=ym.indicator em.compl
  obtain ⟨si,price⟩:=regular Z zm
  obtain ⟨hi,extra⟩:=failed
  have split:F=fun t=>(τ:ℂ)*soft t+hard t:=by
    funext t
    by_cases inE:t∈E <;> simp [F,soft,hard,Z,inE] <;> ring
  have square: (∫t,‖Z t‖^2 ∂μ)≤∫t,‖Y t‖^2 ∂μ:=by
    apply integral_mono ((memLp_two_iff_integrable_sq_norm zm.1).1 zm)
      ((memLp_two_iff_integrable_sq_norm ym.1).1 ym)
    intro t
    by_cases h:t∈Eᶜ
    · simp [Z,h]
    simp [Z,h]
  rw [split]
  refine ⟨(si.const_mul (τ:ℂ)).add hi,?_⟩
  rw [integral_add (si.const_mul (τ:ℂ)) hi,integral_const_mul,mul_add]
  apply (norm_add_le ..).trans
  apply add_le_add _ extra
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg tp]
  exact price.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt square) cp)

end YM.Integration.FVA1Physical.Exchange.RoseDatedReceived
