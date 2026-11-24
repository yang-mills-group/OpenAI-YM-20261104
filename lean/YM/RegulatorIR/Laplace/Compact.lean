import YM.RegulatorIR.Laplace.Pass

/-! Parameter cone small t. Quietly keeping enough Hankel powers to control
unbounded rescaled Gaussian directions at each fixed valuation. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Laplace
open PertExtension Series Series.Radial MeasureTheory Filter Function Set Metric
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical
variable {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
  [NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y]
variable {F K:X × Y→ℝ}
local notation "Z" => (Radial.zone (E:=X × Y))
local notation "W" => (Radial.zone (E:=X))

-- parameter dimension arbitrary; not probability
variable [MeasurableSpace X][BorelSpace X][MeasurableSpace Y][BorelSpace Y](μ:Measure X)[μ.HasTemperateGrowth]
def segment (K F:X × Y→ℝ) (t:ℝ)(r:ℝ)(y:Y):ℝ:= ∫ x in disc t r,projection K F t (x,y) ∂μ
def rates (K F:X × Y→ℝ)(n:ℕ)(y:Y):ℝ:= ∫ x,normTerm K F n (x,y) ∂μ
namespace Readies
variable (H:Readies F K) {D t r q A c:ℝ}
omit μ in
private lemma coin (ht:0<t)(hD:0≤D) (n j:ℕ) (hx:∀ x y,‖y‖ ≤ D → (q+q)*‖x‖^2-c ≤ jet F 2 (x,y))(hq:0<q)(hA:0≤A) (x:X)(y:Y)(hv:‖y‖≤D)(h:‖insertion F K t (x,y)-Zone.eval (integrandSeries F K) n t (x,y)‖ ≤ A*(Z).w (x,y)^j*shade q (x,y)*t^(n+1)):
     ‖projection K F t (x,y) -poly K F n t (x,y)‖ ≤ (A*(1+D)^j*Real.exp (c+q*D^2)*t^(n+1))*bill j q x:=by
 rw [projection,poly,← sub_mul,norm_mul, Real.norm_of_nonneg kernel_pos.le]
 have he := trim_payoff hq hD hx x y hv
 let B := A*((1+D)*(W).w x)^j*t^(n+1)
 apply (mul_le_mul_of_nonneg_right h kernel_pos.le).trans
 calc
  _ ≤ (A*((1+D)*(W).w x)^j*shade q (x,y)*t^(n+1))*kernel F (x,y) := by
     have ht₁:= (Z).high (x,y); have hz := Real.exp_pos (q*‖(x,y)‖^2); have hu:0≤kernel F (x,y):=kernel_pos.le; unfold shade; gcongr; exact Trim_fares hD x y hv
  _ = B*(shade q (x,y)*kernel F (x,y)):=by unfold B; ring
  _ ≤ B* (Real.exp (c+q*D^2)*Real.exp (-q*‖x‖^2)):=mul_le_mul_of_nonneg_left he (by have hh:= (W).high x; unfold B; positivity)
  _ = _:=by unfold B bill; rw [mul_pow]; ring
include H μ
lemma range_cap (H₁:Measurable K)(H₂:Measurable F)(hD:0≤D) (n:ℕ): ∃ δ>0, ∀ r∈Ioo 0 δ,∃ C:ℝ,0 ≤ C ∧ ∀ᶠ t in 𝓝[>] (0:ℝ),∀ y : Y,‖y‖≤ D →
    ‖segment μ K F t r y-Tested.peval (fun i=> rates μ K F i y) n t‖≤ C*t^(n+1):=by
 obtain ⟨c,hc,m,_,Hc⟩:= H.trim.usable hD;let q:=c/2;have hq:0<q:=half_pos hc;rw [show c=q+q from by dsimp [q];ring] at Hc
 obtain ⟨d,A,j,hd,hA,hb⟩:= ((integrand H.fine H.station hq).fits n).cost
 refine ⟨d/(2*(1+D)),by positivity,fun r hr=>?_⟩
 obtain ⟨B,hB,Hu⟩:= wider μ H hD n (n+1) hr.1
 let C := A*(1+D)^j*Real.exp (m+q*D^2); have hR:0≤ C:= by unfold C; positivity
 refine ⟨B+C*∫ x,bill j q x ∂μ,add_nonneg hB (mul_nonneg hR (integral_nonneg (fun x=>bill_nonneg j q x))),?_⟩
 filter_upwards [Tested.eventually_small (show 0< min 1 (d/(2*(1+D))) from lt_min zero_lt_one (by positivity))] with t ht
 intro y hy
 let Q:= disc (E:=X) t r
 let f (x:X):= projection K F t (x,y)
 let g (x:X):= poly K F n t (x,y)
 let A (x:X) := C*t^(n+1)*bill j q x
 have hr':0<t:=ht.1
 have hv: ∀ᵐ x ∂μ.restrict Q, ‖(f-g) x‖≤A x:=by
   filter_upwards [ae_restrict_mem (disc_meas t r)] with x hx
   apply coin hr' hD n j Hc hq hA x y hy
   apply hb _ t hr'
   have hx:= (disc_mem hr'.le r x).mp hx
   have hz := ht.2.trans_le (min_le_right ..)
   have hh : t* (1+‖x‖) ≤ d/(1+D) := by nlinarith [show r<d/(2*(1+D)) from hr.2, show d/(2*(1+D))=d/(1+D)/2 by field_simp]
   calc
    _ ≤ t*((1+D)*(W).w x):=mul_le_mul_of_nonneg_left (Trim_fares hD x y hy) hr'.le
    _ = (t*(1+‖x‖))*(1+D):=by unfold Radial.zone; dsimp; ring
    _ ≤ _ := (le_div_iff₀ (by positivity)).mp hh
 have hi : Integrable A μ := (bill_integrable μ j hq).const_mul _
 have hQ := (H.project μ n t y).1
 have hf : Measurable f:= (projection_meas H₁ H₂ t).comp (measurable_id.prodMk measurable_const)
 have hz:=norm_integral_le_of_norm_le hi.integrableOn hv |>.trans (setIntegral_le_integral hi (Eventually.of_forall (fun x : X=>mul_nonneg (show 0 ≤ C*t^(n+1) by positivity) (bill_nonneg ..))))
 have hA' : IntegrableOn (f-g) Q μ:= hi.integrableOn.mono' (hf.aestronglyMeasurable.sub hQ.integrableOn.1) hv
 have hF := hA'.add hQ.integrableOn
 change IntegrableOn (f-g +g) Q μ at hF; rw [sub_add_cancel] at hF
 change ‖∫ x in Q,f x-g x ∂μ‖≤ _ at hz
 rw [integral_sub hF hQ.integrableOn] at hz
 have he:‖∫ x in Qᶜ,g x ∂μ‖≤B*t^(n+1):= Hu y hy t ⟨ht.1,ht.2.le.trans (min_le_left ..)⟩
 rw [show Tested.peval _ _ t=(∫ x in Q,g x ∂μ)+(∫ x in Qᶜ,g x ∂μ) from ?_,sub_add_eq_sub_sub]
 · apply (norm_sub_le ..).trans
   exact (add_le_add hz he).trans_eq (by unfold A; rw [integral_const_mul]; ring)
 rw [integral_add_compl (disc_meas t r) hQ, show (∫ x,g x ∂μ)= _ from (H.project μ n t y).2]; rfl
end Readies
end YM.RegulatorIR.Laplace
