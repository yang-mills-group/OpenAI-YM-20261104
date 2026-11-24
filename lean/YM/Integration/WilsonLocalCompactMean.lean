import YM.Integration.WilsonLocalCompactHistory

/-! Domination of a signed conditional response by the actual transported
absolute input, on the complete held Wilson fiber. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactMean
open Filter MeasureTheory Lattice RG Wilson
open scoped Classical Topology
variable {X:Type} [MeasurableSpace X] {μ:Measure X} {ρ:X→ℝ}

theorem weighted (inte:Integrable ρ μ) (nn:∀x,0≤ρ x) {h:X→ℝ} (eh:Envelope h):
    Integrable (fun x=>ρ x*h x) μ:=
  (inte.mul_const eh.cost.choose).mono' (inte.aestronglyMeasurable.mul eh.meas.aestronglyMeasurable)
    (Eventually.of_forall fun x=>by
      rw [norm_mul,Real.norm_eq_abs (ρ x),abs_of_nonneg (nn x)]
      exact mul_le_mul_of_nonneg_left (eh.cost.choose_spec _) (nn _))

theorem dominated (inte:Integrable ρ μ) (nn:∀x,0≤ρ x) {f A:X→ℝ}
    (ef:Envelope f) (ea:Envelope A) (bound:∀x,|f x|≤A x):
    |∫x,ρ x*f x ∂μ|≤∫x,ρ x*A x ∂μ:=by
  calc |∫x,ρ x*f x ∂μ|≤∫x,‖ρ x*f x‖ ∂μ:=by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x=>ρ x*f x)
    _≤∫x,ρ x*A x ∂μ:=integral_mono (weighted inte nn ef).norm (weighted inte nn ea) fun x=>by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (nn _),Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (bound x) (nn x)

theorem variation (inte:Integrable ρ μ) (nn:∀x,0≤ρ x) (zp:0<∫x,ρ x ∂μ)
    {h f A:X→ℝ} (eh:Envelope h) (ef:Envelope f) (ea:Envelope A) {c:ℝ}
    (bound:∀x,|h x-f x|≤c*A x):
    let Z:=∫x,ρ x ∂μ
    |(∫x,ρ x*h x ∂μ)/Z-(∫x,ρ x*f x ∂μ)/Z|≤c*((∫x,ρ x*A x ∂μ)/Z):=by
  intro Z
  have ih:=weighted inte nn eh
  have iff:=weighted inte nn ef
  have ia:=weighted inte nn ea
  rw [←sub_div,abs_div,abs_of_pos zp,←mul_div_assoc]
  apply div_le_div_of_nonneg_right _ zp.le
  rw [←integral_sub ih iff]
  calc |∫x,ρ x*h x-ρ x*f x ∂μ|≤∫x,‖ρ x*h x-ρ x*f x‖ ∂μ:=by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x=>ρ x*h x-ρ x*f x)
    _≤∫x,(ρ x*A x)*c ∂μ:=integral_mono (ih.sub iff).norm (ia.mul_const c) fun x=>by
      rw [←mul_sub,Real.norm_eq_abs,abs_mul,abs_of_nonneg (nn _),mul_assoc,mul_comm (A x) c]
      exact mul_le_mul_of_nonneg_left (bound x) (nn x)
    _=c*∫x,ρ x*A x ∂μ:=by rw [integral_mul_const,mul_comm]

theorem centered (inte:Integrable ρ μ) (nn:∀x,0≤ρ x) (unit:(∫x,ρ x ∂μ)=1)
    {f A:X→ℝ} (ef:Envelope f) (ea:Envelope A) (bound:∀x,|f x|≤A x):
    let b:=∫x,ρ x*f x ∂μ
    |b|≤∫x,ρ x*A x ∂μ ∧ (∫x,ρ x*|f x-b| ∂μ)≤2*(∫x,ρ x*A x ∂μ) := by
  intro b
  have v:=dominated inte nn ef ea bound
  have dev:Envelope (fun x=>|f x-b|):=by
    refine ⟨(ef.meas.sub measurable_const).abs,ef.cost.choose+‖b‖,fun x=>?_⟩
    rw [Real.norm_eq_abs,abs_abs,←Real.norm_eq_abs]
    exact (norm_sub_le ..).trans (add_le_add_left (ef.cost.choose_spec x) _)
  refine ⟨v,?_⟩
  calc (∫x,ρ x*|f x-b| ∂μ)≤∫x,ρ x*A x+ρ x*|b| ∂μ:=
      integral_mono (weighted inte nn dev) ((weighted inte nn ea).add (inte.mul_const _)) fun x=>by
        rw [←mul_add]
        exact mul_le_mul_of_nonneg_left ((abs_sub (f x) b).trans (add_le_add_left (bound x) _)) (nn x)
    _ = (∫x,ρ x*A x ∂μ)+|b|:=by rw [integral_add (weighted inte nn ea) (inte.mul_const _),integral_mul_const,unit,one_mul]
    _ ≤ 2*(∫x,ρ x*A x ∂μ):=by change |b|≤_ at v;linarith only [v]

theorem physical {G:Gauge} (C:Family G) (makes:C.Makes) {N per m:ℕ} (live:m<N)
    {f A:Config G (C.side (m+1) per)→ℝ} (ef:Envelope f) (ea:Envelope A) (bound:∀U,|f U|≤A U) (V:Config G (C.side m per)):
    let u:=actualAverage C (N:=N) f V
    let a:=actualAverage C (N:=N) A V
    |u|≤a ∧ actualAverage C (N:=N) (fun U=>|f U-u|) V≤2*a :=
  centered (actualConditionalDensity_integrable C makes live V) (actualConditionalDensity_nonneg C makes live V)
    (actualConditionalDensity_total C makes live V) ef ea bound

end YM.Integration.WilsonLocalCompactMean
