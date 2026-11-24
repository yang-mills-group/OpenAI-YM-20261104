import YM.MSbar.Pole.Analysis.Capacity
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Norm costs for power-exponents in dimensional continuation. For whole jets
with affine dependency on parameters; with a small safety margin from the poles
log correction can be absorbed. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Power
open Function Set Filter MeasureTheory
open scoped Topology ContDiff Classical BigOperators
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma power_bill (L : E →L[ℝ] ℂ) {r : ℝ} (hr : 0<r) (w : ℂ) (x : E) (i : ℕ) :
    let α:= w + L x
    ‖iteratedFDeriv ℝ i (fun x => (r:ℂ)^(w+L x)) x‖ ≤ |Real.log r|^i * (r^α.re) * ‖L‖^i := by
  intro α; let c := Complex.log r; let f (z : ℂ) := Complex.exp (c*z)
  have he (z:ℂ): (r:ℂ)^z=f z:= Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne') _
  have hd : ContDiff ℂ i f := Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  simp_rw [he]
  apply le_trans (iter_affine_le (φ:=f) L w x i ((hd.restrict_scalars ℝ).contDiffAt))
  have hg : ‖iteratedFDeriv ℝ i f α‖= |Real.log r|^i * r ^ α.re := by
    rw [← hd.contDiffAt.restrictScalars_iteratedFDeriv]
    simp only [Function.comp_apply]; rw [ContinuousMultilinearMap.norm_restrictScalars]
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_cexp_const_mul i c]
    change ‖c^i*f α‖ = _; rw [norm_mul,norm_pow,← he,Complex.norm_cpow_eq_rpow_re_of_pos hr]
    unfold c
    rw [← Complex.ofReal_log hr.le]; norm_cast
  exact le_of_eq (congr_arg (· *‖L‖^i) hg)

lemma bounded_logpow {a r : ℝ} (ha : 0 < a) (hp : 0 < r) (hu : r ≤ 1) (i : ℕ) :
    |Real.log r|^i * r^a ≤ ((i:ℝ)/a)^i := by
  by_cases hh : i=0
  · subst i; simpa using Real.rpow_le_one hp.le hu ha.le
  let t : ℝ := a/i; have ht : 0<t := div_pos ha (by positivity)
  have h := Real.abs_log_mul_self_rpow_lt r t hp hu ht
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hp _)] at h
  have hx := pow_le_pow_left₀ (show 0 ≤ |Real.log r| * r^t by positivity) h.le i
  rw [mul_pow,← Real.rpow_mul_natCast hp.le t i] at hx -- check
  rw [show t*(i:ℝ)=a from div_mul_cancel₀ _ (by exact_mod_cast hh),show 1/t=(i:ℝ)/a by simp [t] ] at hx; exact hx

lemma near_bill (L : E →L[ℝ] ℂ) {r : ℝ} (hr : 0<r) (hu : r ≤ 1) (w : ℂ) (x : E) (i : ℕ)
    (hh : 1 ≤ (w+L x).re) :
    ‖iteratedFDeriv ℝ i (fun x => (r:ℂ)^(w+L x)) x‖ ≤ (i:ℝ)^i*‖L‖^i := by
  have hx := power_bill L hr w x i
  refine le_trans (show _ ≤ _ from hx) (mul_le_mul_of_nonneg_right ?_ (by positivity))
  refine (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge_of_imp hr.le hu hh (by simp [hr.ne'])) (show 0≤|Real.log r|^i by positivity)).trans ?_
  simpa using (bounded_logpow zero_lt_one hr hu i)
lemma far_bill (L : E →L[ℝ] ℂ) {r : ℝ} (hr : 1≤r) (w : ℂ) (x : E) (i : ℕ) (M : ℕ)
    (hh : (w+L x).re ≤ (M : ℝ)) :
    ‖iteratedFDeriv ℝ i (fun x => (r:ℂ)^(w+L x)) x‖ ≤ r^(M+i)*‖L‖^i := by
  have hv := zero_lt_one.trans_le hr
  have hx := power_bill L hv w x i
  refine le_trans hx (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have hb : |Real.log r|≤r:= by rw [abs_of_nonneg (Real.log_nonneg hr)]; exact Real.log_le_self hv.le
  rw [pow_add,mul_comm (r^M)]; exact mul_le_mul (pow_le_pow_left₀ (by positivity) hb _) (by simpa using Real.rpow_le_rpow_of_exponent_le hr hh) (by positivity) (pow_nonneg hv.le _)
end YM.MSbar.Pole.Power
