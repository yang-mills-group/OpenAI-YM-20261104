import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Height.Highway

/-! # Recall the grading rate in units of actual fine g

No choice of trajectory, convert at each level in the admitted physical
band. Use a deliberately simple internal degree 4*p (+ old 3) per output
order p, with no divisibility assumptions or losses. This precision upgrade
only applies to the high-arity reserve and doesn't include analytic or
transport losses from the low degrees. Don't bound ψ by g on retained grades.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Vacuum
open RG Pressure Lattice PhysicalNext.Repeat Height
variable {G : Gauge} {L : Side} {s b : ℝ}

/-- In band upper β control suffices; no claim this g is X-scheme coupling. -/
lemma exchange (p : ℕ) (hL : 1 ≤ betaF G s L) (hb : 0 < b) (hu : b ≤ 2*betaF G s L) :
    ((grow G L s)^(4*p))⁻¹ ≤ (Real.sqrt 2 * (Real.sqrt b)⁻¹)^p := by
  let a := betaF G s L
  have ht:0 < a:=zero_lt_one.trans_le hL
  have h : ∀ e : ℝ, (a^e : ℝ)^4=a^(e*4:ℝ):= fun e=> by rw [Real.rpow_mul ht.le]; norm_num
  have he : (grow G L s)^4=a^(3/2:ℝ) := (h (3/8:ℝ)).trans (by norm_num)
  rw [pow_mul, ← inv_pow, he]
  apply pow_le_pow_left₀ (by positivity)
  have hv : a^(1/2:ℝ) ≤ (a^(3/2:ℝ):ℝ):= Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  rw [← Real.sqrt_eq_rpow] at hv
  calc
    _ ≤ (Real.sqrt a)⁻¹ := inv_anti₀ (Real.sqrt_pos.mpr ht) hv
    _ ≤ _ := by
      rw [← div_eq_mul_inv,le_div_iff₀ (Real.sqrt_pos.mpr hb),inv_mul_le_iff₀ (Real.sqrt_pos.mpr ht),mul_comm _ (Real.sqrt 2),← Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
      exact Real.sqrt_le_sqrt hu

/-- Existing theory estimates discussed as order p+1-eta in the admit band.
When g exceeds one (possible on lawfully supplied bands without a front-UV
cut), convert with the recorded sqrt2 cap. -/
lemma admission (p : ℕ) (η : ℝ) (hη : 0 ≤ η) {g : ℝ} (hg : 0 < g) (h1 : g ≤ Real.sqrt 2) :
    g^p ≤ g^((p:ℝ)-η)*(Real.sqrt 2)^η := by
  rw [← Real.rpow_natCast]
  conv_lhs => rw [show (p:ℝ)=((p:ℝ)-η)+η by ring, Real.rpow_add hg]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hg.le h1 hη) (Real.rpow_pos_of_pos hg _).le

end YM.RG01.Vacuum
