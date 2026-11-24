import YM.Integration.FVA1Physical.Wilson.MeasuredTilt

/-! Joint measurability of the normalized twisted physical forest reading. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open MeasureTheory Lattice RG YM.Wilson MSbar.Bulk
open scoped Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {R : Rep G f}
variable {V : Config G c} {σ C δ Λ w : ℝ}
theorem rotated_integral_meas {Ω : Type*} [MeasurableSpace Ω] (adm : Admitted V R S σ C δ Λ w)
    (rot : Ω × Config G f → Config G f) (rhot : Measurable rot)
    (q : Ω × Config G f→ℝ) (mq : Measurable q) (B : Config G f→ℝ) (mB : Measurable B) :
    Measurable (fun θ:Ω=> S.push R.beta (fun U=>q (θ,U)*(R.eval (rot (θ,U))*Real.exp (B U-B (rot (θ,U))))) V/
      (S.push R.beta R.eval V)) := by
  let u := fun p : Ω × Config G f=> S.density R.beta p.2 V *
    (q p*(R.eval (rot p)*Real.exp (B p.2-B (rot p))))
  have hK : Measurable (fun U:Config G f=>S.density R.beta U V) :=
    by
      change Measurable ((fun p : Config G f × Config G c => S.density R.beta p.1 p.2) ∘ (fun U : Config G f => (U,V)))
      exact adm.kernel.meas.comp (show Measurable (fun U : Config G f => (U,V)) from measurable_id.prodMk measurable_const)
  have hU : Measurable u := (hK.comp measurable_snd).mul
    (mq.mul (((R.envelope adm.lawful).meas.comp rhot).mul
       (Real.measurable_exp.comp ((mB.comp measurable_snd).sub (mB.comp rhot)))))
  have hInt : Measurable (fun θ:Ω=>∫ U,u (θ,U) ∂prior G f) :=
    hU.stronglyMeasurable.integral_prod_right'.measurable
  exact hInt.div_const (S.push R.beta R.eval V)
end YM.Integration.FVA1Physical.Wilson
