import YM.RegulatorIR.Laplace.Afloat
import YM.PertExtension.Aspiration

/-! Aspiration coefficients for group-valued input over a parameter slice.
Fixed regulator only! -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Laplace
open PertExtension Series Series.Radial MeasureTheory Filter Function Set Metric
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical
variable {X Y:Type} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
  [NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y]
variable {K F:X × Y→ ℝ}{C D r q α t:ℝ}{k e:ℕ}

local notation "Z" => (Radial.zone (E:=X × Y))
local notation "W" => (Radial.zone (E:=X))
omit [NormedSpace ℝ X][FiniteDimensional ℝ X][NormedSpace ℝ Y][FiniteDimensional ℝ Y] in
lemma Trim_fares (hp:0≤D)(x:X)(y:Y)(h:‖y‖ ≤ D): (Z).w (x,y) ≤ (1+D)*(W).w x:=by
 change 1+max ‖x‖ ‖y‖≤ (1+D)*(1+‖x‖); have he : max ‖x‖ ‖y‖≤ D+‖x‖:=max_le (by linarith) (by linarith [norm_nonneg x]); nlinarith [norm_nonneg x]
omit [FiniteDimensional ℝ X][FiniteDimensional ℝ Y] in
lemma trim_payoff (hr:0<r) (_:0≤D)
  (h:∀ x y, ‖y‖≤ D → (r+r)*‖x‖^2-C ≤ jet F 2 (x,y))(x:X)(y:Y)(hh:‖y‖ ≤ D): shade r (x,y)*kernel F (x,y) ≤ Real.exp (C+r*D^2)*Real.exp (-r*‖x‖^2):= by
 rw [shade, kernel,← Real.exp_add,← Real.exp_add]; apply Real.exp_le_exp.mpr; specialize h x y hh; change r*max ‖x‖ ‖y‖^2+- _≤_
 cases max_cases ‖x‖ ‖y‖ with
 | inl ha=>rw [ha.1];nlinarith
 | inr ha=>rw [ha.1]; have hx:r*‖y‖^2 ≤ r*D^2:=(by gcongr); nlinarith

-- Uniform bounds, monotone from bilinear cost. no claims on extending radii
structure Readies (F K:X × Y→ℝ) : Prop where
 station : Stationary F
 trim : Trim F
 fine : ContDiffAt ℝ ∞ K 0
variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y][BorelSpace Y]
variable (μ:Measure X)[μ.HasTemperateGrowth]
namespace Readies
variable (H:Readies F K)
include H
omit H in
lemma past_parameter {a:X × Y→ℝ}(h:Zone.Invoice Z a)(H':∀ x y, ‖y‖≤D→(r+r)*‖x‖^2-C ≤ jet F 2 (x,y))(hl:0<r)(hD:0≤D):
     ∃ q:ℝ,∃ k:ℕ,0≤q ∧ ∀ x y, ‖y‖≤D → ‖a (x,y)*kernel F (x,y)‖ ≤ q*bill k r x:=by
 obtain ⟨c,n,hc,hb⟩:= h
 refine ⟨c*(1+D)^n*Real.exp (C+r*D^2),n,by positivity, fun x y hx=>?_⟩
 have hp: (1:ℝ) ≤ shade r (x,y):=by unfold shade; apply Real.one_le_exp; positivity
 have ht:kernel F (x,y) ≤ Real.exp (C+r*D^2)*Real.exp (-r*‖x‖^2):= le_trans (le_mul_of_one_le_left kernel_pos.le hp) (trim_payoff hl hD H' x y hx)
 rw [norm_mul, Real.norm_of_nonneg kernel_pos.le]
 have hq :1≤ (Z).w (x,y):= (Z).high (x,y)
 apply (mul_le_mul ((hb (x,y)).trans (show _*(Z).w (x,y)^n≤ c*((1+D)*(W).w x)^n by gcongr; exact Trim_fares hD x y hx)) ht kernel_pos.le (by have hx := (W).high x; positivity)).trans_eq
 unfold bill; rw [mul_pow]; ring
include μ
lemma protects (n) (y:Y): Integrable (fun x=> normTerm K F n (x,y)) μ:=by
 obtain ⟨c,hc,b,hb,Hb⟩:= H.trim.usable (norm_nonneg y);let r:=c/2; have hr:0<r:=half_pos hc;rw [show c=r+r from by dsimp [r];ring] at Hb
 obtain ⟨t,k,ht,h⟩:= past_parameter ((integrand H.fine H.station hr).invoice n) Hb hr (norm_nonneg y)
 exact ((bill_integrable μ k hr).const_mul t).mono' ((show Continuous fun x:X=>normTerm K F n (x,y) from (Smooth.continuousTerms ..).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable) (Eventually.of_forall (fun x=>h x y le_rfl))

lemma project (n)(t : ℝ)(y:Y):Integrable (fun x=> poly K F n t (x,y)) μ ∧
    (∫ x,poly K F n t (x,y) ∂μ)= ∑ i∈Finset.range (n+1),t^i*(∫ x,normTerm K F i (x,y) ∂μ):=by
 have hh (x) : poly K F n t (x,y)= ∑ i∈ Finset.range (n+1), t^i * normTerm K F i (x,y):=by rw [poly]; simp only [normTerm, Zone.eval, Finset.sum_mul,smul_eq_mul, mul_assoc]
 simp_rw [hh]
 constructor
 · exact integrable_finsetSum _ fun i _=>(H.protects μ i y).const_mul _
 simp_rw [integral_finsetSum _ (fun i _=>(H.protects μ i y).const_mul (t^i)),integral_const_mul]

lemma wider (hD:0≤D)(n N:ℕ)(hr:0<r) : ∃ c:ℝ, 0 ≤ c ∧ ∀ y, ‖y‖≤D → ∀ t ∈ Ioc (0:ℝ) 1,
     ‖∫ x in (disc t r)ᶜ,poly K F n t (x,y) ∂μ‖ ≤ c*t^N:=by
 obtain ⟨c,hc,b,hb,Hb⟩:= H.trim.usable hD;let q:=c/2; have hq:0<q:=half_pos hc;rw [show c=q+q from by dsimp [q];ring] at Hb
 obtain ⟨A,k,hA,Hz⟩:= H.station.coeffBound H.fine n
 let B:= A*(1+D)^k *Real.exp (b+q*D^2) * (r⁻¹)^N
 have hB:0≤B:=by unfold B; positivity
 refine ⟨B * ∫ x,bill (k+N) q x ∂μ,mul_nonneg hB (integral_nonneg (fun x=>bill_nonneg _ _ x)),?_⟩
 intro y hy t ht
 let g(x:X):=B*t^N*bill (k+N) q x
 have ht':0<t:=ht.1
 have hi: Integrable g μ:= (bill_integrable μ (k+N) hq).const_mul _
 apply le_trans (norm_integral_le_of_norm_le hi.integrableOn ?_) ((setIntegral_le_integral hi (Eventually.of_forall (fun x=>mul_nonneg (mul_nonneg hB (by positivity)) (bill_nonneg _ _ x)))).trans_eq (by unfold g; rw [integral_const_mul]; ring))
 filter_upwards [ae_restrict_mem (disc_meas t r).compl] with x (hx : x∈(disc t r)ᶜ)
 have hp : r ≤ t*‖x‖:= not_lt.mp (hx ∘ (disc_mem ht'.le r x).mpr)
 have hw: t*(W).w x*(r⁻¹)≥1 := by apply (le_mul_inv_iff₀ hr).mpr; change 1*r ≤ t*(1+‖x‖); linarith
 rw [poly,norm_mul, Real.norm_of_nonneg kernel_pos.le]
 have hC := trim_payoff hq hD Hb x y hy
 have hZ : kernel F (x,y) ≤ _:= le_trans (le_mul_of_one_le_left kernel_pos.le (show 1 ≤ shade q (x,y) by unfold shade;apply Real.one_le_exp;positivity)) hC
 let v:= Real.exp (-q*‖x‖^2)
 have hhA: A*(Z).w (x,y)^k ≤ A*((1+D)*(W).w x)^k:=by have := (Z).high (x,y); gcongr; exact Trim_fares hD x y hy
 have he:=mul_le_mul ((Hz (x,y) t ht'.le ht.2).trans hhA) hZ kernel_pos.le (show 0≤ A*((1+D)*(W).w x)^k by have := (W).high x; positivity)
 apply he.trans
 apply le_trans (le_mul_of_one_le_right (show 0≤ A*((1+D)*(W).w x)^k * (Real.exp (b + q * D^2) * Real.exp (-q*‖x‖^2)) by have := (W).high x; positivity) (one_le_pow₀ (n:=N) hw))
 · dsimp only [g,bill,B]; rw [pow_add]; simp only [mul_pow]; exact le_of_eq (by ring)
 
end Readies
end YM.RegulatorIR.Laplace
