import YM.OPE.Compatible.Mason.Tithe
/-! # averaged Stature. Integrability and heavy estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
open Silt Cloud PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Spells
variable {X Y:Type}{t s:ℝ}{i k:ℕ} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X]
open Lav Flock
section
variable [NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y][MeasurableSpace Y][BorelSpace Y]
variable (B:Law Y)(ν:Measure Y)[ν.IsAddHaarMeasure]
local notation "η"=> quart B ν
local notation "Z" => Radial.zone (E:=Y)
omit [MeasurableSpace X][BorelSpace X][FiniteDimensional ℝ X][MeasurableSpace Y][BorelSpace Y][FiniteDimensional ℝ Y][NormedSpace ℝ X][NormedSpace ℝ Y] in
private lemma clamp {C:ℝ}(f:X×Y→ℝ)(ht:0 ≤ C)(h:∀ v,‖f v‖ ≤ C*(1+‖v‖)^i)(x:X)(y:Y)(hr:‖x‖ ≤ t): ‖f (x,y)‖≤ C*(1+t)^i*(1+‖y‖)^i:=by
       have he:0≤t:= le_trans (norm_nonneg _) hr; rw [mul_assoc C,←mul_pow]; refine (h _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (?_) _) ht); change 1+max ‖x‖ ‖y‖≤_; have hw : max ‖x‖ ‖y‖≤ t+‖y‖:= max_le (by linarith only [hr,norm_nonneg y]) (by linarith only [he]); nlinarith only [hw,mul_nonneg he (norm_nonneg y)]
omit [MeasurableSpace Y][BorelSpace Y][FiniteDimensional ℝ Y] in lemma statureBase {p:Y→ℝ}(h:Continuous p)(hz:(Z).Invoice p): Stature p 0:=by
       refine ⟨(by simpa using h),fun {j} hj v=>?_⟩; obtain rfl : j=0:=by omega
       rw[Fline_zero]; exact hz
variable {p:X×Y→ℝ}
omit [MeasurableSpace X][BorelSpace X][FiniteDimensional ℝ X][MeasurableSpace Y][BorelSpace Y][FiniteDimensional ℝ Y] in
lemma stat_slice (h:Stature p i)(x:X): Stature (fun y:Y=>p (x,y)) 0:=by
       obtain ⟨C,k,hc,hz⟩:= h.invoice; exact statureBase (h.smooth.continuous.comp (continuous_const.prodMk continuous_id)) ⟨C*(1+‖x‖)^k,k,by positivity,fun s=> clamp p hc hz x s le_rfl⟩
omit [MeasurableSpace X][BorelSpace X][FiniteDimensional ℝ X] in
lemma decaf (h:Stature p i): Stature (fun x=> B.average ν (fun y=>p (x,y))) 0:=by
       obtain ⟨C,k,hc,hz⟩:= h.invoice; let F:=fun y:Y=>(1+‖y‖)^k; have hf:Integrable F η:=by apply goodX; exact (continuous_const.add continuous_norm).pow k; exact ⟨1,k,by norm_num,fun x=>by change ‖(1+‖x‖)^k‖≤1*(1+‖x‖)^k; rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),one_mul]⟩
       simp_rw [← has_p]; apply statureBase
       · apply continuous_iff_continuousAt.mpr; intro x; let D := C*(1+(‖x‖+1))^k; refine continuousAt_of_dominated (bound:=fun y=> D*F y) (Eventually.of_forall (fun _=>(stat_slice h _).smooth.continuous.aestronglyMeasurable)) ?_ (hf.const_mul _) (Eventually.of_forall (fun y=> (h.smooth.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt))
         filter_upwards [show ∀ᶠ s:X in (𝓝 x), ‖s‖<‖x‖+1 from continuous_norm.continuousAt.tendsto.eventually (eventually_lt_nhds (show ‖x‖<‖x‖+1 by linarith))] with s hs; exact Eventually.of_forall (fun y => clamp p hc hz s y hs.le)
       let t:=C*a_ η F; have hK : 0 ≤ a_ η F:= integral_nonneg (fun i=> by unfold F; positivity);
       refine ⟨t,k,mul_nonneg hc hK,fun i=>?_⟩; refine (norm_integral_le_integral_norm _).trans ?_; calc
           _ ≤ ∫ y:Y,C*(1+‖i‖)^k*F y ∂η := integral_mono ((Irite (Ppu B ν (stat_slice h _))).norm) (hf.const_mul _) (fun y=>clamp p hc hz i y le_rfl)
           _= t*(1+‖i‖)^k:=by rw[integral_const_mul]; unfold t a_; ring
end
end YM.OPE.Borealis
