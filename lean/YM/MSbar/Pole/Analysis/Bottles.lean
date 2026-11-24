import YM.MSbar.Pole.Analysis.Capacity

/-! Convenient builders for repeatedly forming integrable seminorms. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory
open scoped Topology ContDiff Classical Interval BigOperators

variable {E F A : Type} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup A]
  [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ A]
variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} {p q : Price E} {U : Set E} {f : Z → E → A}

lemma pullBarrel [IsFiniteMeasure μ] {t : Set F} {r w : Price F} (L : Z → E →L[ℝ] F) (T : Z → F) {F' : F → A}
    (hp : Packet t r w F') (ho : IsOpen U) (hc : ContinuousOn p.val U)
    {C : ℝ} (hC : 0 ≤ C) (hL : ∀ᵐ z ∂μ, ‖L z‖ ≤ C)
    (ht : ∀ᵐ z ∂μ, ∀ x∈U, let y:= T z+L z x; y∈t ∧ r y ≤ C*p x ∧ q x ≤ C*w y)
    (hm : ∀ x∈U, AEStronglyMeasurable (fun z => F' (T z+L z x)) μ) :
    Barrel μ U p q (fun z x => F' (T z+L z x)) := by
  refine ⟨ho,hc,ht.mono (fun z hv x hx => (hp.smooth _ (hv x hx).1).comp x (contDiffAt_const.add (L z).contDiff.contDiffAt)),hm,fun i k => ?_⟩
  obtain ⟨b,e,hb,h⟩:= hp.budget i k
  refine ⟨fun _=>C^i*C^k*b*C^e, e, Eventually.of_forall fun _=>by positivity, integrable_const _,?_⟩
  filter_upwards [ht,hL] with z hv he x hx
  let y := T z+L z x; let l := ‖iteratedFDeriv ℝ i F' y‖
  have hl : 0 ≤ l := norm_nonneg _
  have hh := h _ (hv x hx).1
  have hz := iter_affine_le (L z) (T z) x i (hp.localn i (hv x hx).1)
  have hf : l * w y ^ k ≤ b * (C*p x)^e := hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (r.pos _).le (hv x hx).2.1 _) hb)
  refine le_trans (mul_le_mul (hz.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) he _) hl))
    (pow_le_pow_left₀ (q.pos _).le (hv x hx).2.2 _) (pow_nonneg (q.pos _).le _) (mul_nonneg hl (pow_nonneg hC _))) ?_
  change l*C^i*(C*w y)^k ≤ _
  calc
    _ = C^i*C^k*(l*w y^k) := by rw [mul_pow]; ring
    _ ≤ C^i*C^k*(b*(C*p x)^e) := mul_le_mul_of_nonneg_left hf (by positivity)
    _ = _ := by rw [mul_pow]; ring

lemma comp_affine_bill {t : Set F} (L : E →L[ℝ] F) (T : F) {F' : F → A} {r w}
    (hp : Packet t r w F')
    (ht : MapsTo (fun x => T+ L x) U t)
    (hr : Bills U p 1 (fun x => r (T+L x))) (hw : Bills U (w.back (fun x => T+L x)) 1 (fun x => q x)) :
    Packet U p q (fun x => F' (T+L x)) := by
  refine ⟨fun x hx => (hp.smooth _ (ht hx)).comp x (contDiffAt_const.add L.contDiff.contDiffAt),fun i=>?_⟩
  have hf := ((hp.budget i).pull ht).norm
  refine (((hf.growing hr).weakening (b:=q) hw).mul (Bills.const (‖L‖^i))).dominates (fun x hx => ?_)
  exact (iter_affine_le L T x i (hp.localn i (ht hx))).trans (le_abs_self _)
end YM.MSbar.Pole
