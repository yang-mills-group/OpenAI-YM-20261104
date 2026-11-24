import YM.FormalOPE.RG10.Inherit.Screens
/-!
 # Stationary moments for multi-diagram probe 

 Unlike in accepted `Orb` basic API footprint, price may be merely measurable on complement of
 a stationarity patch; inherited global gap enough. All constants may depend on index/period
 and all other data. Also adapters to varying power-series schedules will use this formulation.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.StationaryMarks
open Function Filter Topology Set Metric MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Inherit Push.Loops Chart Lattice RG
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{I:Type}[Fintype I]

local notation "μ"=>physical G I
local notation "ν"=>tangent G I
local notation "E"=>Direction G I

 def dollar (A: Spending G I)(O : Spending G I) (t:ℝ)(x) := O x * Real.exp (-A x/t^2)
variable (P:ChartRatio G) (A O:Spending G I)
 def offer : E→ℝ:= (jacobian P)*(O ∘ expLinks G I)
 def summing : ℕ→ℝ:= Radial.moment ν (offer P O) (A ∘ expLinks G I)
 def scale (G :Gauge) (I:Type)[Fintype I](t:ℝ): ℝ:=(t^(Module.finrank ℝ (Direction G I)))⁻¹
 def journal (t:ℝ): ℝ:= scale G I t * ∫ x:Configuration G I,dollar A O t x ∂μ
-- scale marked by arbitrary price instead of top Orb.account. local Smooth.
variable {A O} (C:Credential A)(h:Curtain O)
include C h in
lemma measurable_charge (t:ℝ): Measurable (dollar A O t):= h.meas.mul (Measurable.exp (C.meas.neg.div_const _))
include C h in
lemma endowment (t:ℝ) : Integrable (dollar A O t) μ := by
 obtain ⟨R,hr⟩:= h.bounded; apply (integrable_const R).mono' (measurable_charge C h t).aestronglyMeasurable (Eventually.of_forall fun x=>?_)
 unfold dollar; rw [norm_mul,Real.norm_eq_abs (Real.exp ..),abs_of_pos (Real.exp_pos _)]; exact (mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (C.nn x)) (sq_nonneg _)))).trans (hr _)
variable {P} (L : LocalRatio P)
-- interior as in Orb. Estimate from accepted `rescale_estimate`.
lemma in_scale {t r:ℝ}(ht:0<t) (f:E→ℝ):
 scale G I t * (∫ u in ball 0 r, f u ∂ν) = (∫ u in disc t r, f (t • u) ∂ν):= by
 let S:Set E:=ball 0 r
 have h (u:E): S.indicator f (t•u)=(disc t r).indicator (fun v=>f (t•v)) u:=by
    by_cases hh:t•u∈S
    · rw [Set.indicator_of_mem hh,Set.indicator_of_mem (show u ∈ disc t r from hh)]
    rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem (show u ∉ disc t r from hh)]
 rw [←integral_indicator (f:=f) (isOpen_ball.measurableSet), scale, ←smul_eq_mul, ←Measure.integral_comp_smul_of_nonneg ν (S.indicator f) t (hR:=ht.le)]; simp_rw [h]; rw [integral_indicator (disc_meas t r)]
include L C h in
lemma interiorized {t r:ℝ}(ht:0<t)(hr: r<small G P)(hs:0<r):
 scale G I t * (∫ u in chamber G I r,dollar A O t u ∂μ)=partialSum ν (offer P O) (A ∘ expLinks G I) r t:=by
 rw [Ratio.chamber_integral L (dollar A O t) (measurable_charge C h t) hr hs, in_scale ht]
 unfold partialSum
 congr 1
 ext u
 rw [projection_eq]; simp only [offer,Pi.mul_apply,Function.comp_apply,dollar, mul_assoc]
end YM.FormalOPE.RG10.StationaryMarks
