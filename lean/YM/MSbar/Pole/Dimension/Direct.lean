import YM.MSbar.Pole.Dimension.Lift
import YM.MSbar.Pole.Analysis.Exponents
import YM.MSbar.Pole.Analysis.Compensate
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Initial Mellin integral with the exponent in the right half-plane. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Radial
open Function Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Classical
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- This is normalized to unit value on `exp(-r^2)`. -/
def j (F : ℝ→ℂ) (w : ℂ) : ℂ := 2/Complex.Gamma (w/2)* ∫ t : ℝ in Ioi (0:ℝ), F t*(t:ℂ)^(w-1)
def jKernel (f : ℝ×E→ℂ) (L : E →L[ℝ] ℂ) (w : ℂ) (t : ℝ) (x : E) :=
    f (t,x)*(t:ℂ)^(w+L x-1)
local notation "ω" => volume.restrict (Ioi (0:ℝ))
variable {p q : Price E} {f : ℝ×E→ℂ} {U : Set E} (o : IsOpen U) (c : ContinuousOn p.val U)
variable (L : E →L[ℝ] ℂ) (w : ℂ)
include o c
lemma jBarrel (h : Packet (Ioi (0:ℝ) ×ˢ U) (p.back Prod.snd) (Moment q) f) (M : ℕ)
    (hw : ∀ x∈U, (w+ L x-1).re ∈ Icc 1 (M:ℝ)) : Barrel ω U p q (jKernel f L w) := by
  let F (t:ℝ) (x:E) := f (t,x); let G (t:ℝ) (x:E) := (t:ℂ)^((w-1)+L x)
  suffices Barrel ω U p q (fun t x=>F t x*G t x) by
    unfold jKernel; simpa only [F,G,sub_add_eq_add_sub] using this
  refine leibniz ?_ ?_ o c ?_ ?_ ?_
  · intro x hx; refine ContinuousOn.aestronglyMeasurable (s:=Ioi (0:ℝ)) ?_ measurableSet_Ioi
    exact fun t ht => (((h.smooth (t,x) ⟨ht,hx⟩).continuousAt).comp (f:=fun v : ℝ => (v,x)) (x:=t) (show ContinuousAt (fun v : ℝ => (v,x)) t from by fun_prop)).continuousWithinAt
  · intro x hx; apply ContinuousOn.aestronglyMeasurable (s:=Ioi (0:ℝ)) _ measurableSet_Ioi
    intro t ht
    exact (show ContinuousAt (G · x) t by
      unfold G; exact ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const (Complex.ofReal_mem_slitPlane.mpr ht)).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x hx
    exact (h.smooth (t,x) ⟨ht,hx⟩).comp x (contDiffAt_const.prodMk contDiffAt_id)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x hx
    refine (show ContDiff ℝ ∞ (G t) from ?_).contDiffAt; unfold G
    simp_rw [Complex.cpow_def_of_ne_zero (x:=(t:ℂ)) (by have hu : 0<t:= ht; exact_mod_cast hu.ne')]
    fun_prop
  intro i j k; let R := ((volume:Measure ℝ).integrablePower); let N := max k (R+M+j)
  obtain ⟨b,e,hb,hv⟩:=h.budget i N
  let D := ‖ContinuousLinearMap.inr ℝ ℝ E‖^i
  have hD : 0≤D := by unfold D; positivity
  let C := ((j:ℝ)^j+1)*‖L‖^j
  have hc : 0 ≤ C := by unfold C; positivity
  let P (t:ℝ) := 1+‖t‖
  have hP t : 1 ≤ P t := by dsimp [P]; simp
  let μ (t : ℝ) := (P t ^ R)⁻¹
  have hb' : Integrable μ ω := by
    have hm := Measure.integrable_pow_neg_integrablePower (volume : Measure ℝ)
    change Integrable (fun x : ℝ=> (1+‖x‖)^(-(R:ℝ))) at hm
    have he (x:ℝ) : (1+‖x‖)^(-(R:ℝ)) = μ x:=by unfold μ P; rw [Real.rpow_neg (by positivity),Real.rpow_natCast]
    simp_rw [he] at hm
    exact hm.integrableOn
  refine ⟨fun t=>μ t*(C*b*D),e,Eventually.of_forall (fun t => ?_),hb'.mul_const _,?_⟩
  · dsimp [μ]; exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans (hP _)) _)) (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht: 0<t) x hx
  have ha : ‖iteratedFDeriv ℝ j (G t) x‖ ≤ C*P t^(M+j) := by
    obtain (hx'|hx'):= le_total t 1
    · have hf := Power.near_bill L ht hx' (w-1) x j (by rw [sub_add_eq_add_sub]; exact (hw x hx).1)
      refine le_trans (show ‖iteratedFDeriv ℝ j (G t) x‖≤_ from hf) (le_trans (b:=C) ?_ ?_)
      · unfold C; gcongr; linarith
      exact le_mul_of_one_le_right hc (one_le_pow₀ (hP _))
    have hf := Power.far_bill L hx' (w-1) x j M (by rw [sub_add_eq_add_sub]; exact (hw x hx).2)
    refine le_trans (show ‖iteratedFDeriv ℝ j (G t) x‖≤_ from hf) ?_
    rw [mul_comm]; -- which
    have hz : ‖L‖^j ≤ C := le_mul_of_one_le_left (by positivity) (by simp)
    have hk : t ≤ P t := by unfold P; rw [Real.norm_of_nonneg ht.le]; simp
    gcongr
  let W := ‖iteratedFDeriv ℝ i f (t,x)‖
  have hW : 0 ≤ W := norm_nonneg _
  have hh : ‖iteratedFDeriv ℝ i (F t) x‖ ≤ W * D := iter_right_le (h.localn i (mem_prod.mpr ⟨ht,hx⟩))
  have hp' : W * (P t * q x)^N ≤ b*p x^e:= hv (t,x) ⟨ht,hx⟩
  change _ ≤ μ t * _ * _; rw [mul_comm (μ t),mul_right_comm (b:=μ t)]
  change _ ≤ _ * _⁻¹; rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (zero_lt_one.trans_le (hP t)) _)]
  calc
    _ ≤ W*D * (C*P t^(M+j)) * q x^k * P t^R := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul hh ha (norm_nonneg _) (by positivity)) (pow_nonneg (q.pos _).le _))
        (pow_nonneg (zero_le_one.trans (hP _)) _)
    _ = W * (P t^(R+M+j)*q x^k) * (C*D) := by simp only [pow_add]; ring
    _ ≤ (b * p x^e)*(C*D) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      refine le_trans ?_ hp'; rw [mul_pow]; gcongr
      · exact pow_nonneg (q.pos _).le _
      · exact hP _
      · exact le_max_right ..
      · exact q.large _
      · exact le_max_left ..
    _ = _ := by ring
end YM.MSbar.Pole.Radial
