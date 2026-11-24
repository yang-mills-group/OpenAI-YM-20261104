import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import YM.RG.Bounded

/-!
# Integrated error prices

Our first matching theorem will use `Lp` norms calculated with the whole Wilson law or true
unnormalized-density/coarse probability quotient. These are numerical error estimates; there is
no assumption here of compatibility with a regular/forced reserve or derivative estimate. We
record `Envelope` additionally because some proofs use calculus and its boundedness guarantees
(prices in `Envelope` needn't be uniform in regulator at all). In particular `LpCharge` never
uses fallback values of integrals of nonintegrable quantities under these finite measures.
-/

set_option autoImplicit false
noncomputable section

namespace YM.MatchingR2
open Function MeasureTheory Filter RG
open scoped Topology ContDiff BigOperators ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable {p q : ℕ} {c d : ℝ} {f g : Ω → ℝ}

section envelope
omit [IsFiniteMeasure μ]
theorem envelope_comp {X : Type*} [MeasurableSpace X] {g : Ω → X} {f : X → ℝ}
    (hf : Envelope f) (hg : Measurable g) : Envelope (f ∘ g) := by
  obtain ⟨M, hM⟩ := hf.cost
  exact ⟨hf.meas.comp hg, M, fun x => hM (g x)⟩

theorem envelope_sub (hf : Envelope f) (hg : Envelope g) : Envelope fun i => f i - g i := by
  simp_rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem envelope_norm (hf : Envelope f) : Envelope fun i => ‖f i‖ := by
  obtain ⟨M, hM⟩ := hf.cost
  exact ⟨hf.meas.norm, M, fun x => by simpa using hM x⟩

theorem envelope_pow (hf : Envelope f) (p : ℕ) : Envelope fun x => f x ^ p := by
  induction p with
  | zero => simpa using Envelope.const (V := Ω) 1
  | succ p ih => simp_rw [pow_succ]; exact ih.mul hf

theorem envelope_fsum {ι : Type*} {s : Finset ι} (f : ι → Ω → ℝ)
    (h : ∀ i∈s, Envelope (f i)) : Envelope fun v => ∑ i∈s, f i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Envelope.const (V := Ω) 0)
  | insert i s hi ih => simpa [hi] using ((h i (by simp)).add (ih (fun j hj => h j (by simp [hj]))))
end envelope

lemma envelopeLp (μ : Measure Ω) [IsFiniteMeasure μ] (p : ℝ≥0∞) (hf : Envelope f) :
    MemLp f p μ := by
  obtain ⟨M, hM⟩ := hf.cost
  exact MemLp.of_bound hf.meas.aestronglyMeasurable M (Eventually.of_forall hM)

/-- Integrated `L^p` estimate in the *given* finite measure. -/
structure LpCharge (μ : Measure Ω) (p : ℕ) (f : Ω → ℝ) (C : ℝ) : Prop where
  exponent : 0 < p
  finite : IsFiniteMeasure μ
  env : Envelope f
  cost : lpNorm f p μ ≤ C

namespace LpCharge

omit [IsFiniteMeasure μ] in
lemma nonneg (h : LpCharge μ p f c) : 0 ≤ c := lpNorm_nonneg.trans h.cost
lemma relax (h : LpCharge μ p f c) (hh : c ≤ d) : LpCharge μ p f d := ⟨h.exponent, inferInstance, h.env,h.cost.trans hh⟩
lemma add (h : LpCharge μ p f c) (k : LpCharge μ p g d) :
    LpCharge μ p (fun i => f i + g i) (c + d) :=
  ⟨h.exponent, inferInstance, h.env.add k.env,
    (lpNorm_add_le (g := g) (envelopeLp μ p h.env) (by exact_mod_cast (Nat.succ_le_of_lt h.exponent))).trans
      (add_le_add h.cost k.cost)⟩
lemma neg (h : LpCharge μ p f c) : LpCharge μ p (fun i => - f i) c :=
  ⟨h.exponent, inferInstance, h.env.neg, by rw [lpNorm_fun_neg]; exact h.cost⟩
lemma sub (h : LpCharge μ p f c) (k : LpCharge μ p g d) :
    LpCharge μ p (fun i => f i - g i) (c + d) := by simp_rw [sub_eq_add_neg]; exact h.add k.neg
lemma norm (h : LpCharge μ p f c) : LpCharge μ p (fun i => ‖f i‖) c :=
  ⟨h.exponent, inferInstance, envelope_norm h.env, by rw [lpNorm_norm h.env.meas.aestronglyMeasurable]; exact h.cost⟩
lemma scale (h : LpCharge μ p f c) (a : ℝ) : LpCharge μ p (fun i => a * f i) (‖a‖ * c) :=
  ⟨h.exponent, inferInstance, (Envelope.const a).mul h.env, by
    change lpNorm (a • f) _ _ ≤ _
    rw [lpNorm_const_smul]
    exact mul_le_mul_of_nonneg_left h.cost (norm_nonneg _)⟩
lemma fsum {ι : Type*} {s : Finset ι} (f : ι → Ω → ℝ) (c : ι → ℝ)
    (h : ∀ i∈s, LpCharge μ p (f i) (c i)) (hp : 0 < p) :
    LpCharge μ p (fun v => ∑ i∈s, f i v) (∑ i∈s, c i) :=
  ⟨hp, inferInstance, envelope_fsum f (fun i hi => (h i hi).env), by
    simp_rw [← Finset.sum_apply]; exact
      (lpNorm_sum_le (s := s) (f := f) (fun i hi => envelopeLp μ p (h i hi).env)
        (by exact_mod_cast (Nat.succ_le_of_lt hp))).trans
      (Finset.sum_le_sum (fun i hi => (h i hi).cost))⟩
lemma zero (μ : Measure Ω) [IsFiniteMeasure μ] (hp : 0 < p) : LpCharge μ p (fun _ => 0) 0 :=
  ⟨hp, inferInstance, Envelope.const _, by simp⟩
omit [IsFiniteMeasure μ] in
lemma const [IsProbabilityMeasure μ] (hp : 0 < p) (a : ℝ) :
    LpCharge μ p (fun _ => a) ‖a‖ :=
  ⟨hp, inferInstance, Envelope.const _, by simp [lpNorm_const' (p := (p:ℝ≥0∞)) (by positivity) (by simp)]⟩
omit [IsFiniteMeasure μ] in
lemma lower [IsProbabilityMeasure μ] (h : LpCharge μ p f c) (hq : 0 < q) (he : q ≤ p) :
    LpCharge μ q f c :=
  ⟨hq, inferInstance, h.env, le_trans (b:=lpNorm f p μ) (by
    simp_rw [← toReal_eLpNorm h.env.meas.aestronglyMeasurable]
    exact ENNReal.toReal_mono (envelopeLp μ _ h.env).eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le (by exact_mod_cast he) h.env.meas.aestronglyMeasurable)) h.cost⟩

lemma monotone (h : LpCharge μ p f c) (hg : Envelope g) (he : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖f x‖) :
    LpCharge μ p g c :=
  ⟨h.exponent, inferInstance, hg, le_trans (b := lpNorm f p μ) (by
    rw [← toReal_eLpNorm hg.meas.aestronglyMeasurable, ← toReal_eLpNorm h.env.meas.aestronglyMeasurable]
    exact ENNReal.toReal_mono (envelopeLp μ _ h.env).eLpNorm_ne_top (eLpNorm_mono_ae he)) h.cost⟩

lemma monoReal (h : LpCharge μ p f c) (hg : Envelope g) (he : ∀ᵐ x ∂μ, ‖g x‖ ≤ f x) :
    LpCharge μ p g c := h.monotone hg (he.mono (fun _ hx => hx.trans (Real.le_norm_self _)))

lemma mul (h : LpCharge μ (2*p) f c) (k : LpCharge μ (2*p) g d) :
    LpCharge μ p (fun i => f i * g i) (c*d) := by
  have hp := h.exponent
  have hpos : 0 < p := by omega
  set P : ℝ≥0∞ := ↑(2*p : ℕ) with hP
  haveI : ENNReal.HolderTriple P P p := ENNReal.HolderTriple.of_toReal (by
    rw [hP]
    simp only [Nat.cast_mul, Nat.cast_ofNat, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
    constructor
    all_goals first | positivity | field_simp; ring)
  refine ⟨hpos, inferInstance, h.env.mul k.env,?_⟩
  apply le_trans (b := lpNorm f P μ*lpNorm g P μ)
  · change lpNorm (f • g) _ _ ≤ _
    have he (p : ℝ≥0∞) : MemLp (f • g) p μ := envelopeLp μ p (h.env.mul k.env)
    rw [← toReal_eLpNorm (he p).1, ← toReal_eLpNorm h.env.meas.aestronglyMeasurable,
      ← toReal_eLpNorm k.env.meas.aestronglyMeasurable, ← ENNReal.toReal_mul]
    apply ENNReal.toReal_mono
      (ENNReal.mul_ne_top (envelopeLp μ _ h.env).eLpNorm_ne_top (envelopeLp μ _ k.env).eLpNorm_ne_top)
    exact eLpNorm_smul_le_mul_eLpNorm k.env.meas.aestronglyMeasurable h.env.meas.aestronglyMeasurable
  exact mul_le_mul h.cost k.cost lpNorm_nonneg h.nonneg

-- Keep the finite measure hypothesis: only using the real norm in the integrable regime.
lemma measurable_price_identity (hf : Envelope f) (hp : 0 < p) :
    lpNorm f p μ ^ p = ∫ i, ‖f i‖ ^ p ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by exact_mod_cast hp.ne')
    (ENNReal.natCast_ne_top _) (envelopeLp μ p hf).1, ENNReal.toReal_natCast]
  simp_rw [Real.rpow_natCast]; rw [←Real.rpow_natCast ( (_:ℝ)^ (_:ℝ))]
  exact Real.rpow_inv_rpow (integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)) (by positivity)
lemma of_integral (hf : Envelope f) (hc : 0 ≤ c) (hp : 0 < p) (h : ∫ i, ‖f i‖^p ∂μ ≤ c^p) :
    LpCharge μ p f c := by
  rw [← measurable_price_identity hf hp] at h
  exact ⟨hp, inferInstance, hf, le_of_pow_le_pow_left₀ hp.ne' hc h⟩
lemma integral_pay (h : LpCharge μ p f c) : ∫ i, ‖f i‖^p ∂μ ≤ c^p :=
  (measurable_price_identity h.env h.exponent).symm.trans_le (pow_le_pow_left₀ lpNorm_nonneg h.cost p)

end LpCharge
end YM.MatchingR2
