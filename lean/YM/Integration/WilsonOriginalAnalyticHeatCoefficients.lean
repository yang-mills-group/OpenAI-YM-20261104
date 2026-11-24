import YM.Integration.WilsonOriginalAnalyticFourierTail

/-! Smoothness step of the compact Fourier upgrade. A single finite
sampling bank and its measured Wilson heater work for all data satisfying
the analytic and tested estimates on that bank. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAnalyticHeatCoefficients
open Filter Function Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb
open scoped Topology BigOperators
open WilsonOriginalDatedJetSamples (date)

private theorem upper {G : Gauge} {warm : ℝ → ℝ} (paid : Coupling G warm) (n : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ᶠ s : ℝ in atTop, ∀ i : Fin n,
      0 ≤ warm (date s i) ∧ s * warm (date s i) ≤ H := by
  let r := fun s : ℝ => Real.exp (-(s^2))
  have ht : Tendsto r atTop trail := WilsonOriginalDatedJetSamples.radii
  have sq : Tendsto (fun s : ℝ => (s*warm (r s))^2) atTop (𝓝 G.slopeConstant⁻¹) := by
    simpa [r,Function.comp_def,LogV,Real.log_inv,mul_pow] using paid.running.comp ht
  let L := Real.sqrt G.slopeConstant⁻¹
  have hl : 0 ≤ L := Real.sqrt_nonneg _
  have measured : Tendsto (fun s : ℝ => s*warm (r s)) atTop (𝓝 L) := by
    apply ((Real.continuous_sqrt.tendsto _).comp sq).congr'
    filter_upwards [ht.eventually paid.positive,eventually_ge_atTop (0:ℝ)] with s hp hs
    exact Real.sqrt_sq (mul_nonneg hs hp.le)
  refine ⟨(n+1)*(L+1),by positivity,Filter.eventually_all.mpr fun i => ?_⟩
  let m : ℝ := (i.val : ℝ)+1
  have hm : 0 < m := by dsimp [m];positivity
  have hmn : m ≤ (n:ℝ)+1 := by dsimp [m];exact_mod_cast Nat.add_le_add_right i.isLt.le 1
  have go : Tendsto (fun s : ℝ => s/m) atTop atTop := by
    simpa only [div_eq_inv_mul,id_eq] using
      (Tendsto.const_mul_atTop (inv_pos.mpr hm) (tendsto_id : Tendsto id (atTop : Filter ℝ) atTop))
  filter_upwards [go.eventually ((tendsto_order.mp measured).2 (L+1) (by linarith)),
    (ht.comp go).eventually paid.positive] with s hb hp
  refine ⟨hp.le,?_⟩
  change s*warm (r (s/m)) ≤ _
  calc
    _ = m*(s/m*warm (r (s/m))) := by field_simp [hm.ne']
    _ ≤ m*(L+1) := mul_le_mul_of_nonneg_left hb.le hm.le
    _ ≤ _ := mul_le_mul_of_nonneg_right hmn (by linarith)

/-- For any demanded inverse power choose the internal crop first. Here
s^12 is the actual frequency, and d is the fixed Fourier test loss.
The bound holds uniformly over all signed coefficient and reading arrays. -/
theorem original {G : Gauge} {warm : ℝ → ℝ} (hG : G.Simple) (paid : Coupling G warm)
    (q k d : ℕ) (j : Fin (q+1)) (order : k+j.val+12*d+1 ≤ q)
    (A D c C : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hc : 0 < c) (hC : 0 ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, ∀ (f y : Fin (q+1) → ℂ),
      (∀ i, let u := warm (date s i)
        ‖y i‖ ≤ A*(u⁻¹)^2*Real.exp (D*(u⁻¹)^4-c*s^6*u)) →
      (∀ i, let u := warm (date s i)
        ‖y i-∑ z : Fin (q+1), (u:ℂ)^z.val*f z‖ ≤ C*u^q*(1+s^12)^d) →
      s^k*‖f j‖ ≤ ε := by
  obtain ⟨H,hH,temp⟩ := upper paid (q+1)
  obtain ⟨B,hB,bank⟩ := WilsonOriginalDatedJetSamples.original hG paid (q+1)
  let δ := ε/(2*(1+B*(q+1)))
  have hden : 0 < 2*(1+B*((q:ℝ)+1)) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have sumFee : B*((q:ℝ)+1)*(2*δ) ≤ ε := by
    have hx : δ*(2*(1+B*((q:ℝ)+1))) = ε := div_mul_cancel₀ ε hden.ne'
    linarith
  let cash := C*2^d*H^q
  have hcash : 0 ≤ cash := by dsimp [cash];positivity
  have analytic := WilsonOriginalAnalyticFourierTail.original hG paid (q+1) (k+j.val)
    A D c hA hD hc hδ
  filter_upwards [temp,bank,analytic,eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop (cash/δ)] with s warmth fit fall hs late f y ysize tested
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have base : 1+s^12 ≤ 2*s^12 := by linarith [(one_le_pow₀ hs : (1:ℝ) ≤ s^12)]
  have one (i : Fin (q+1)) : s^(k+j.val)*
      (‖y i‖ + ‖y i-∑ z : Fin (q+1), (warm (date s i):ℂ)^z.val*f z‖) ≤ 2*δ := by
    let u := warm (date s i)
    let e := ‖y i-∑ z : Fin (q+1), (u:ℂ)^z.val*f z‖
    obtain ⟨hu,hot⟩ := warmth i
    have poly : (1+s^12)^d ≤ 2^d*(s^12)^d := by
      simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ 1+s^12) base d
    have test : e ≤ C*u^q*(2^d*(s^12)^d) := (tested i).trans
      (mul_le_mul_of_nonneg_left poly (mul_nonneg hC (pow_nonneg hu _)))
    have heat : s^q*u^q ≤ H^q := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (mul_nonneg hs0.le hu) hot q
    have ex : s^(k+j.val)*(s^12)^d*s ≤ s^q := by
      rw [← pow_mul,← pow_add,← pow_succ]
      exact pow_le_pow_right₀ hs order
    have tour : s^(k+j.val)*e*s ≤ cash := calc
      _ ≤ s^(k+j.val)*(C*u^q*(2^d*(s^12)^d))*s := by gcongr
      _ = (C*2^d)*((s^(k+j.val)*(s^12)^d*s)*u^q) := by ring
      _ ≤ (C*2^d)*(s^q*u^q) := by gcongr
      _ ≤ cash := mul_le_mul_of_nonneg_left heat (by positivity)
    have small : s^(k+j.val)*e ≤ δ := by
      apply (le_div_iff₀ hs0).2 at tour
      exact tour.trans ((div_le_iff₀ hs0).2 (by
        simpa only [mul_comm s] using (div_le_iff₀ hδ).1 late))
    have tail := (mul_le_mul_of_nonneg_left (ysize i) (pow_nonneg hs0.le (k+j.val))).trans (fall i)
    rw [mul_add]; change _+s^(k+j.val)*e ≤ _
    linarith
  calc
    _ ≤ s^k*(|s|^j.val*B*∑ i, (‖y i‖+‖y i-∑ z : Fin (q+1),
        (warm (date s i):ℂ)^z.val*f z‖)) :=
      mul_le_mul_of_nonneg_left (fit f y j) (pow_nonneg hs0.le _)
    _ = B*∑ i, s^(k+j.val)*(‖y i‖+‖y i-∑ z : Fin (q+1),
        (warm (date s i):ℂ)^z.val*f z‖) := by rw [← Finset.mul_sum,pow_add,abs_of_pos hs0];ring
    _ ≤ B*∑ _ : Fin (q+1), 2*δ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => one i) hB
    _ ≤ ε := by simpa [mul_assoc] using sumFee

end YM.Integration.WilsonOriginalAnalyticHeatCoefficients

