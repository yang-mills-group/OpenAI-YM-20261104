import YM.Integration.WilsonPositionScaleLawPhysicalClockRatio

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawPhysicalThermalRatio
open Function Filter Set Spec Table Extraction OPE Climb PhysMS Trace.Pilot Maxwell Maxwell.Free
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawCompactNative (bothHomes positive)
open WilsonPositionScaleLawGuardGradeClock (age)
open scoped Topology Classical
variable {G:Gauge}
theorem signed [RangeSpec] {θ:ℝ→ℝ} (simple:G.Simple)(heat:Coupling G θ)(sign:∀ᶠr in trail,0<θ r):
    Tendsto (fun z:ℝ×Ratio=>θ z.1/θ (z.2.val*z.1)) sweep (𝓝 1) := by
  have a : Tendsto (fun r=>θ r^2/θ r^2) trail (𝓝 1) :=
    tendsto_const_nhds.congr' (sign.mono (fun r h=>(div_self (pow_ne_zero 2 h.ne')).symm))
  have sq := WilsonPositionScaleLawPhysicalClockRatio.anchored (b:=fun r=>θ r^2) simple heat one_ne_zero a
  have root : Tendsto (fun z:ℝ×Ratio=>Real.sqrt (θ z.1^2/θ (z.2.val*z.1)^2)) sweep (𝓝 1) := by
    simpa only [Function.comp_def,Real.sqrt_one] using (Real.continuous_sqrt.continuousAt.tendsto.comp sq)
  refine root.congr' ?_
  filter_upwards [(tendsto_fst (f:=trail) (g:=(⊤:Filter Ratio))).eventually sign,
    WilsonPositionScaleLawCompactNative.bothHomes.eventually sign] with z near far
  rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq near.le,Real.sqrt_sq far.le]
theorem measured {I:Type*}{l:Filter I}{b θ:ℝ→ℝ}{κ:ℝ}(nk:κ≠0)
    (paid:Tendsto (fun r=>b r/θ r^2) trail (𝓝 κ)) (r s:I→ℝ)(near:Tendsto r l trail)(far:Tendsto s l trail):
    Tendsto (fun i=>(b (r i)/b (s i))/(θ (r i)/θ (s i))^2) l (𝓝 1) := by
  have cash := (paid.comp near).div (paid.comp far) nk
  rw [div_self nk] at cash
  refine cash.congr' (Eventually.of_forall (fun i=>?_))
  change (b (r i)/θ (r i)^2)/(b (s i)/θ (s i)^2)=(b (r i)/b (s i))/(θ (r i)/θ (s i))^2
  rw [div_pow]
  exact div_div_div_comm _ _ _ _

end YM.Integration.WilsonPositionScaleLawPhysicalThermalRatio
end
