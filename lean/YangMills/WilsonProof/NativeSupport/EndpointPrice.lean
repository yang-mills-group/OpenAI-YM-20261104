import YangMills.WilsonProof.NativeSupport.LayerPressure

/-! The exponential-moment bound used to compare real thermal readings. All
four partition masses are the tagged `mass` of the original traversal. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open Finset MeasureTheory Lattice RG Wilson RGComparison.Core16
open WilsonUniformUnmarkedInletConnectedCovariance WilsonUniformUnmarkedInletSignedResponse
open scoped Classical BigOperators
variable {G : Gauge} {n c : Side}

private lemma mass_mono (d : Descent n c) (ok : d.OK G) (β : ℕ → ℝ)
    (V : Config G c) {f h : Config G n → ℝ} (hf : Continuous f) (hh : Continuous h)
    (le : ∀ U, f U ≤ h U) : mass d β f V ≤ mass d β h V := by
  apply sum_le_sum
  intro t _
  apply integral_mono (d.path_integrable ok β t f hf V) (d.path_integrable ok β t h hh V)
  intro x
  exact mul_le_mul_of_nonneg_left (le _) (mul_nonneg (d.probability_nonneg ..) (Real.exp_pos _).le)

private lemma mass_affine (d : Descent n c) (ok : d.OK G) (β : ℕ → ℝ) (V : Config G c)
    {f : Config G n → ℝ} (hf : Continuous f) (a b : ℝ) :
    mass d β (fun U => a*f U+b) V = a*mass d β f V+b*mass d β 1 V := by
  simp only [mass, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  have h1 := d.path_integrable ok β t (1 : Config G n → ℝ) continuous_const V
  have h2 := d.path_integrable ok β t f hf V
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h2.const_mul a) (h1.const_mul b)]
  congr 1
  funext x
  simp only [Descent.integrand, Pi.one_apply]
  ring

private lemma exp_mass_lower (d : Descent n c) (ok : d.OK G) (β : ℕ → ℝ) (V : Config G c)
    {f : Config G n → ℝ} (hf : Continuous f) (s : ℝ) :
    let μ := mass d β f V / mass d β 1 V
    Real.exp (s*μ)*mass d β 1 V ≤ mass d β (fun U => Real.exp (s*f U)) V := by
  intro μ
  let a := Real.exp (s*μ)*s
  let b := Real.exp (s*μ)*(1-s*μ)
  have comp : ∀ U, a*f U+b ≤ Real.exp (s*f U) := by
    intro U
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (s*(f U-μ))) (Real.exp_pos (s*μ)).le
    rw [← Real.exp_add, show s*μ+s*(f U-μ)=s*f U by ring] at h
    exact (show a*f U+b=Real.exp (s*μ)*(s*(f U-μ)+1) by dsimp [a,b]; ring).le.trans h
  have le := mass_mono d ok β V ((continuous_const.mul hf).add continuous_const)
    ((continuous_const.mul hf).rexp) comp
  change mass d β (fun U => a*f U+b) V ≤ mass d β (fun U => Real.exp (s*f U)) V at le
  rw [mass_affine d ok β V hf] at le
  have mu : μ * mass d β 1 V = mass d β f V := div_mul_cancel₀ _ (positive d ok β V).ne'
  rw [← mu] at le
  exact (show Real.exp (s*μ)*mass d β 1 V=a*(μ*mass d β 1 V)+b*mass d β 1 V by
    dsimp only [a,b]; ring).le.trans le

theorem path_jensen (d : Descent n c) (ok : d.OK G) (β : ℕ → ℝ) (V : Config G c)
    {f : Config G n → ℝ} (hf : Continuous f) (s : ℝ) :
    s*(mass d β f V / mass d β 1 V) ≤
      Real.log (mass d β (fun U => Real.exp (s*f U)) V) - Real.log (mass d β 1 V) := by
  have h := Real.log_le_log (mul_pos (Real.exp_pos _) (positive d ok β V)) (exp_mass_lower d ok β V hf s)
  rw [Real.log_mul (Real.exp_pos _).ne' (positive d ok β V).ne', Real.log_exp] at h
  linarith

/-- Intensive variational comparison at a real interpolated array, for the
actual empirically averaged fine observable or any other continuous fine `f`.
The extensive calibrated log MGF appears only after division by terminal volume. -/
theorem intensive_response {A : Levels G} {p N k : ℕ} (T : Slices A p) (hk : k ≤ N)
    (β v : ℕ → ℝ) (top : v (traversal T hk).depth = 0) {η : ℝ} (hη : 0 ≤ η)
    (offset : ∀ j, 0 < j → j < (traversal T hk).depth → |v j| ≤ η)
    (V : Config G (A.S.side k p)) {f : Config G (A.S.side N p) → ℝ}
    (hf : Continuous f) (s : ℝ) :
    let d := traversal T hk
    let vol : ℝ := Fintype.card (Site (A.S.side k p))
    let Y := line β v 1
    let μ (B : ℕ → ℝ) := mass d B f V / mass d B 1 V
    s*(μ Y - μ β)/vol ≤
      (Real.log (mass d β (fun U => Real.exp (s*f U)) V) - Real.log (mass d β 1 V) - s*μ β)/vol +
      2*((d.depth * ((A.S.side N p).val^4 * 4) : ℕ) / vol) * (η * (A.clock.kernel.penalty * 2)) := by
  intro d vol Y μ
  let F (U : Config G (A.S.side N p)) := Real.exp (s*f U)
  have hF : Continuous F := (continuous_const.mul hf).rexp
  have pos := positive d (traversal_ok T hk) β V
  have lo : 0 < mass d β F V := (mul_pos (Real.exp_pos _) pos).trans_le
    (exp_mass_lower d (traversal_ok T hk) β V hf s)
  have hi := pressure_step T hk β v top hη offset V hF (fun U => (Real.exp_pos _).le) lo
  have unit := pressure_step T hk β v top hη offset V (f := 1) continuous_const
    (fun _ => zero_le_one) pos
  have J := div_le_div_of_nonneg_right (path_jensen d (traversal_ok T hk) Y V hf s)
    (show 0 ≤ vol by dsimp [vol]; positivity)
  change |Real.log (mass d Y F V)-Real.log (mass d β F V)| / vol ≤ _ at hi
  change |Real.log (mass d Y 1 V)-Real.log (mass d β 1 V)| / vol ≤ _ at unit
  have vn : 0 ≤ vol := by dsimp [vol]; positivity
  have N1 := div_le_div_of_nonneg_right (le_abs_self (Real.log (mass d Y F V)-Real.log (mass d β F V))) vn
  have N2 := div_le_div_of_nonneg_right (neg_le_abs (Real.log (mass d Y 1 V)-Real.log (mass d β 1 V))) vn
  change s*(μ Y)/vol ≤ (Real.log (mass d Y F V)-Real.log (mass d Y 1 V))/vol at J
  change _ ≤ (Real.log (mass d β F V)-Real.log (mass d β 1 V)-s*μ β)/vol+_
  let toll : ℝ := ((d.depth * ((A.S.side N p).val^4 * 4) : ℕ) / vol) * (η * (A.clock.kernel.penalty * 2))
  have h1 : (Real.log (mass d Y F V)-Real.log (mass d β F V))/vol ≤ toll := N1.trans hi
  have h2 : -(Real.log (mass d Y 1 V)-Real.log (mass d β 1 V))/vol ≤ toll := N2.trans unit
  calc
    _ = s*μ Y/vol - s*μ β/vol := by ring
    _ ≤ (Real.log (mass d Y F V)-Real.log (mass d Y 1 V))/vol - s*μ β/vol := sub_le_sub_right J _
    _ = (Real.log (mass d β F V)-Real.log (mass d β 1 V)-s*μ β)/vol +
        (Real.log (mass d Y F V)-Real.log (mass d β F V))/vol +
        -(Real.log (mass d Y 1 V)-Real.log (mass d β 1 V))/vol := by ring
    _ ≤ (Real.log (mass d β F V)-Real.log (mass d β 1 V)-s*μ β)/vol + toll + toll :=
      add_le_add (add_le_add_right h1 _) h2
    _ = _ := by dsimp only [toll]; ring

end YM.Integration.InletSusceptibility
