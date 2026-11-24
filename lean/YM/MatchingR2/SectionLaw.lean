import YM.MatchingR2.LawPrice
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Section law at one step

Direct finite-dimensional normalized densities, *not* choosing some conditional expectation
representative or a convention for off-slice tags. Need measurability and Envelope checks also
for e.g. differentiated uses. No charge of a sup envelope when passing integrated budgets.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MatchingR2
open Filter Function MeasureTheory Set RG
open scoped Topology BigOperators ENNReal
variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

section
variable (μ : Measure Ω) (u : Ω → ℝ)
def fromWeight := μ.withDensity (fun x => ENNReal.ofReal (u x))
variable (hn : ∀ x, 0 ≤ u x)
include hn
lemma fromWeight_prob (h : Integrable u μ) (hz : ∫ x, u x ∂μ = 1) :
    IsProbabilityMeasure (fromWeight μ u) where
  measure_univ := by rw [fromWeight, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ, ← ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall hn), hz]; simp

lemma fromWeight_integral (h : Measurable u) (f : Ω → ℝ) :
    ∫ x, f x ∂fromWeight μ u = ∫ x, u x * f x ∂μ := by
  rw [fromWeight, integral_withDensity_eq_integral_toReal_smul h.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (hn _), smul_eq_mul]
end

-- passing nontrivial `MemLp` tests across this bridge will require qualifying integrals.
theorem fromWeight_active (μ : Measure Ω) {u : Ω → ℝ} (h : Measurable u) :
    ∀ᵐ x ∂fromWeight μ u, 0 < u x := by
  rw [fromWeight, ae_withDensity_iff h.ennreal_ofReal]
  exact Eventually.of_forall (fun x hx => by
    exact ENNReal.ofReal_pos.mp (bot_lt_iff_ne_bot.mpr hx))

section
variable (μ : Measure Ω) [IsFiniteMeasure μ]
theorem envelope_section (f : Ω × X → ℝ) (hf : Envelope f) (x : Ω) : Envelope fun i => f (x,i) :=
  envelope_comp hf (measurable_const.prodMk measurable_id)
lemma envelope_integrated (f : X × Ω → ℝ) (hf : Envelope f) :
    Envelope fun x => ∫ i, f (x,i) ∂μ := by
  obtain ⟨c,hc⟩ := hf.cost
  refine ⟨(StronglyMeasurable.integral_prod_right (f := curry f)
    (by simpa using hf.meas.stronglyMeasurable : StronglyMeasurable (uncurry (curry f)))).measurable,
    μ.real Set.univ * c, fun x => ?_⟩
  simpa only [integral_const, smul_eq_mul] using
    (le_trans (norm_integral_le_integral_norm _)
      (integral_mono ((envelope_section _ hf x).integrable μ |>.norm) (integrable_const c) (fun i => hc (x,i))))
end

-- Think Ω : all coarse configurations, X : all fine configs with tags.
-- z is marg. actual density. Proof gives literal pointwise denominator identities.
structure Middle (μ : Measure Ω) (ν : Measure X) (z : Ω → ℝ) (u : Ω × X → ℝ) : Prop where
  envelope : Envelope u
  nn (k) : 0 ≤ u k
  proper (x) : 0 < z x
  section_id (x) : ∫ y, u (x,y) ∂ν = z x
  total : ∫ x, z x ∂μ = 1

variable {μ : Measure Ω} {ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {z : Ω → ℝ} {u : Ω × X → ℝ}

namespace Middle
-- We keep IsFiniteMeasure μ and ν on APIs for these estimates.
variable (M : Middle μ ν z u)
include M
omit M in
lemma payroll {μ : Measure Ω} {ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {z : Ω → ℝ} {u : Ω × X → ℝ} (M : Middle μ ν z u) : Envelope z := by
  suffices hh : Envelope (fun x => ∫ y, u (x,y) ∂ν) by
    simpa only [M.section_id] using hh
  exact envelope_integrated ν u M.envelope

lemma integral_one : ∫ x, u x ∂μ.prod ν = 1 := by
  rw [integral_prod _ (M.envelope.integrable _)]
  simp_rw [M.section_id]
  exact M.total
lemma both : IsProbabilityMeasure (fromWeight (μ.prod ν) u) :=
  fromWeight_prob _ _ M.nn (M.envelope.integrable _) M.integral_one
lemma marginal : IsProbabilityMeasure (fromWeight μ z) :=
  fromWeight_prob _ _ (fun i => (M.proper i).le) (M.payroll.integrable _) M.total

omit M in
def conditional (ν : Measure X) (z : Ω → ℝ) (u : Ω × X → ℝ) (x : Ω) :=
  fromWeight ν fun y => u (x,y) * (z x)⁻¹
omit M in
lemma each {μ : Measure Ω} {ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {z : Ω → ℝ} {u : Ω × X → ℝ} (M : Middle μ ν z u) (x : Ω) : IsProbabilityMeasure (conditional ν z u x) := by
  unfold conditional
  refine fromWeight_prob ν _ (fun y => mul_nonneg (M.nn _) (by exact inv_nonneg.mpr (M.proper _).le))
    ((envelope_section u M.envelope x).integrable _ |>.mul_const _) ?_
  rw [integral_mul_const, M.section_id, mul_inv_cancel₀ (M.proper x).ne']

omit M in
/-- Conditional answer on observables. Use only with integrable inputs. -/
def answer (ν : Measure X) (z : Ω → ℝ) (u : Ω × X → ℝ) (f : Ω × X → ℝ) (x : Ω) :=
  ∫ y, f (x,y) ∂conditional ν z u x
omit M in
lemma answer_id {μ : Measure Ω} {ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {z : Ω → ℝ} {u : Ω × X → ℝ} (M : Middle μ ν z u) (x) (f : Ω × X → ℝ) : answer ν z u f x =
    (∫ y, u (x,y)*f (x,y) ∂ν) / z x := by
  have he := M.proper x
  rw [answer, conditional, fromWeight_integral _ _ (fun y => mul_nonneg (M.nn (x,y)) (inv_nonneg.mpr he.le))
    (((envelope_section u M.envelope x).mul (Envelope.const _)).meas)]
  rw [div_eq_mul_inv, ← integral_mul_const]
  apply integral_congr_ae; filter_upwards with i
  change u (x,i) * (z x)⁻¹ * f (x,i) = _; ring
lemma charged (f : Ω × X → ℝ) (h : Envelope f) : Envelope (answer ν z u f) := by
  obtain ⟨C,hC⟩ := h.cost
  refine ⟨?_,C,fun x => ?_⟩
  · rw [funext fun x => M.answer_id x f]
    exact (envelope_integrated ν _ (M.envelope.mul h)).meas.div M.payroll.meas
  letI := M.each x
  apply (norm_integral_le_integral_norm _).trans
  have he := integral_mono ((envelope_section f h x).integrable (conditional ν z u x) |>.norm) (integrable_const C)
    (fun i => hC (x,i))
  simpa using he
lemma saves (f : Ω × X → ℝ) (h : Envelope f) :
    ∫ k, answer ν z u f k ∂fromWeight μ z = ∫ p, f p ∂fromWeight (μ.prod ν) u := by
  rw [fromWeight_integral _ _ (fun x => (M.proper x).le) M.payroll.meas,
    fromWeight_integral _ _ M.nn M.envelope.meas, integral_prod _ ((M.envelope.mul h).integrable _)]
  congr 1; ext1 x; rw [M.answer_id]; field_simp [(M.proper x).ne']
lemma charge {f : Ω × X → ℝ} {p : ℕ} {c : ℝ} (hf : LpCharge (fromWeight (μ.prod ν) u) p f c) :
    LpCharge (fromWeight μ z) p (answer ν z u f) c := by
  letI := M.both; letI := M.marginal
  have hp := hf.exponent
  apply LpCharge.of_integral (M.charged f hf.env) hf.nonneg hp
  let y (xx : Ω × X) := ‖f xx‖ ^ p
  have hz : Envelope y := envelope_pow (envelope_norm hf.env) p
  refine le_trans (b:=∫ i, answer ν z u y i ∂fromWeight μ z) ?_ ((M.saves y hz).trans_le hf.integral_pay)
  apply integral_mono ((envelope_pow (envelope_norm (M.charged f hf.env)) p).integrable _) ((M.charged y hz).integrable _)
  intro x
  let F := fun i => f (x,i)
  let rho := conditional ν z u x
  letI : IsProbabilityMeasure rho := M.each x
  have he : Envelope F := envelope_section f hf.env x
  have hv : lpNorm F 1 rho ≤ lpNorm F p rho := by
    have h0 := (LpCharge.lower (μ:=rho) (p:=p) (q:=1) (c:=lpNorm F p rho)
      (f:=F) ⟨hp,inferInstance,he,le_rfl⟩ (by simp) (by omega))
    simpa using h0.cost
  change ‖∫ i, F i ∂rho‖ ^ p ≤ ∫ i, ‖F i‖ ^ p ∂rho
  rw [lpNorm_one_eq_integral_norm he.meas.aestronglyMeasurable] at hv
  exact (pow_le_pow_left₀ (norm_nonneg _) ((norm_integral_le_integral_norm _).trans hv) p).trans_eq
    (LpCharge.measurable_price_identity he hp)
end Middle
end YM.MatchingR2
