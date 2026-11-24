import YM.Integration.WilsonPhysicalHistoryRetainedSpringRoot
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Joint moments of the retained action vertices on one physical conditional field. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace YM.Integration.OriginalMarkedRunAction

private theorem jointMoment {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [Nonempty I]
    (μ : Measure Ω) (f : I → Ω → ℂ) (c : I → ℝ)
    (meas : ∀ i, AEStronglyMeasurable (f i) μ) (hc : ∀ i, 0 ≤ c i)
    (moment : ∀ i, Integrable (fun z => ‖f i z‖ ^ Fintype.card I) μ ∧
      ∫ z, ‖f i z‖ ^ Fintype.card I ∂μ ≤ c i ^ Fintype.card I) :
    Integrable (fun z => ∏ i, f i z) μ ∧
      ∫ z, ‖∏ i, f i z‖ ∂μ ≤ ∏ i, c i := by
  classical
  let n := Fintype.card I
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have undo (u : ℝ≥0∞) : (u ^ n) ^ (n : ℝ)⁻¹ = u := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_inv_cancel₀ hn, ENNReal.rpow_one]
  have each (i : I) :
      ∫⁻ z, ‖f i z‖ₑ ^ n ∂μ ≤ (ENNReal.ofReal (c i)) ^ n := by
    have eq : ENNReal.ofReal (∫ z, ‖f i z‖ ^ n ∂μ) =
        ∫⁻ z, ‖f i z‖ₑ ^ n ∂μ := by
      rw [ofReal_integral_eq_lintegral_ofReal (moment i).1
        (Filter.Eventually.of_forall fun z => pow_nonneg (norm_nonneg (f i z)) n)]
      simp only [n, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [← eq, ← ENNReal.ofReal_pow (hc i)]
    exact ENNReal.ofReal_le_ofReal (moment i).2
  have weights : ∑ _i : I, (n : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn
  have holder := ENNReal.lintegral_prod_norm_pow_le (μ := μ) Finset.univ
    (f := fun i z => ‖f i z‖ₑ ^ n)
    (fun i _ => (meas i).aemeasurable.enorm.pow_const _) weights
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg n))
  have joint : ∫⁻ z, ‖∏ i, f i z‖ₑ ∂μ ≤ ENNReal.ofReal (∏ i, c i) := by
    calc
      _ = ∫⁻ z, ∏ i, (‖f i z‖ₑ ^ n) ^ (n : ℝ)⁻¹ ∂μ := by
        apply lintegral_congr
        intro z
        rw [← ofReal_norm, norm_prod, ENNReal.ofReal_prod_of_nonneg (fun i _ => norm_nonneg _)]
        simp only [undo, ofReal_norm]
      _ ≤ _ := holder
      _ ≤ ∏ i, ((ENNReal.ofReal (c i)) ^ n) ^ (n : ℝ)⁻¹ := by
        gcongr with i
        exact each i
      _ = _ := by simp only [undo, ENNReal.ofReal_prod_of_nonneg (fun i _ => hc i)]
  have whole := Finset.univ.aestronglyMeasurable_fun_prod (fun i _ => meas i)
  refine ⟨⟨whole, joint.trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  rw [integral_norm_eq_lintegral_enorm whole]
  simpa [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => hc i)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top joint

private theorem splitWord {I : Type*} [Fintype I] [DecidableEq I] (a e : I → ℂ) :
    (∏ i, (e i + a i)) - ∏ i, a i =
      ∑ t ∈ (Finset.univ : Finset (Finset I)).erase ∅,
        ∏ i, if i ∈ t then e i else a i := by
  classical
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ ∅)]
  simp only [Finset.notMem_empty, if_false]
  rw [Fintype.prod_add]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_ite]
  have comp : tᶜ = Finset.univ.filter (fun i => i ∉ t) := by ext i; simp
  simp [comp]


/-- Price the full signed change of a finite list of occupied vertices on a single law.
Each term uses precisely the individual root prices of its occurrences. -/
theorem joined_vertex_errors {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    [Nonempty I] [DecidableEq I] (μ : Measure Ω) (a t : I → Ω → ℂ) (c e : I → ℝ)
    (ma : ∀ i, AEStronglyMeasurable (a i) μ) (mt : ∀ i, AEStronglyMeasurable (t i) μ)
    (hc : ∀ i, 0 ≤ c i) (he : ∀ i, 0 ≤ e i)
    (actual : ∀ i, Integrable (fun z => ‖a i z‖ ^ Fintype.card I) μ ∧
      ∫ z, ‖a i z‖ ^ Fintype.card I ∂μ ≤ c i ^ Fintype.card I)
    (error : ∀ i, Integrable (fun z => ‖t i z - a i z‖ ^ Fintype.card I) μ ∧
      ∫ z, ‖t i z - a i z‖ ^ Fintype.card I ∂μ ≤ e i ^ Fintype.card I) :
    Integrable (fun z => (∏ i, t i z) - ∏ i, a i z) μ ∧
      (∫ z, ‖(∏ i, t i z) - ∏ i, a i z‖ ∂μ) ≤
        ∑ u ∈ (Finset.univ : Finset (Finset I)).erase ∅,
          ∏ i, if i ∈ u then e i else c i := by
  classical
  let slots (u : Finset I) (i : I) (z : Ω) :=
    if i ∈ u then t i z - a i z else a i z
  let price (u : Finset I) (i : I) := if i ∈ u then e i else c i
  let word (u : Finset I) (z : Ω) := ∏ i, slots u i z
  let masks := (Finset.univ : Finset (Finset I)).erase ∅
  have bought (u : Finset I) : Integrable (word u) μ ∧
      (∫ z, ‖word u z‖ ∂μ) ≤ ∏ i, price u i := by
    apply jointMoment μ (slots u) (price u)
    · intro i
      by_cases hi : i ∈ u
      · simpa [slots, hi, Pi.sub_def] using (mt i).sub (ma i)
      · simpa [slots, hi] using ma i
    · intro i
      by_cases hi : i ∈ u <;> simp [price, hi, he, hc]
    · intro i
      by_cases hi : i ∈ u
      · simpa [slots, price, hi] using error i
      · simpa [slots, price, hi] using actual i
  have same (z : Ω) :
      (∏ i, t i z) - ∏ i, a i z = ∑ u ∈ masks, word u z := by
    simpa [masks, slots, word] using splitWord (fun i => a i z) (fun i => t i z - a i z)
  simp_rw [same]
  have summed := integrable_finsetSum masks (fun u _ => (bought u).1)
  refine ⟨summed, ?_⟩
  calc
    _ ≤ ∫ z, ∑ u ∈ masks, ‖word u z‖ ∂μ :=
      integral_mono summed.norm (integrable_finsetSum masks fun u _ => (bought u).1.norm)
        (fun _ => norm_sum_le ..)
    _ = ∑ u ∈ masks, ∫ z, ‖word u z‖ ∂μ :=
      integral_finsetSum masks fun u _ => (bought u).1.norm
    _ ≤ _ := Finset.sum_le_sum fun u _ => (bought u).2


/-- A nonempty set of Taylor replacements contains at least one remainder.
The full product of the spatial occurrence prices survives the grade estimate. -/
private theorem occupied_budget {I : Type*} [Fintype I] [DecidableEq I]
    (c e b : I → ℝ) {δ : ℝ} (d0 : 0 ≤ δ) (d1 : δ ≤ 1)
    (c0 : ∀ i, 0 ≤ c i) (e0 : ∀ i, 0 ≤ e i)
    (base : ∀ i, c i ≤ b i) (extra : ∀ i, e i ≤ δ * b i) :
    (∑ u ∈ (Finset.univ : Finset (Finset I)).erase ∅,
        ∏ i, if i ∈ u then e i else c i) ≤
      (((Finset.univ : Finset (Finset I)).erase ∅).card : ℝ) * δ * ∏ i, b i := by
  classical
  have b0 (i : I) := (c0 i).trans (base i)
  let masks := (Finset.univ : Finset (Finset I)).erase ∅
  have bill (u : Finset I) (mem : u ∈ masks) :
      (∏ i, if i ∈ u then e i else c i) ≤ δ * ∏ i, b i := by
    have ne : u ≠ ∅ := (Finset.mem_erase.mp mem).1
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr ne))
    calc
      _ ≤ ∏ i, (if i ∈ u then δ else (1 : ℝ)) * b i := by
        apply Finset.prod_le_prod
        · intro i _
          split <;> first | exact e0 i | exact c0 i
        · intro i _
          by_cases hi : i ∈ u
          · simpa [hi] using extra i
          · simpa [hi] using base i
      _ = δ ^ u.card * ∏ i, b i := by
        rw [Finset.prod_mul_distrib, Finset.prod_ite]
        simp
      _ ≤ _ := by
        rw [hk, pow_succ]
        exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left d0 (pow_le_one₀ d0 d1))
          (Finset.prod_nonneg fun i _ => b0 i)
  calc
    _ ≤ ∑ _u ∈ masks, δ * ∏ i, b i := Finset.sum_le_sum bill
    _ = _ := by simp [masks, nsmul_eq_mul, mul_assoc]

/-- The signed joint coefficient at a bounded correlated insertion. The common grade δ
is spent once, and each occupied vertex retains its original spatial tariff. -/
theorem joined_vertex_price {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [Nonempty I]
    [DecidableEq I] (μ : Measure Ω) (a t : I → Ω → ℂ) (c e b : I → ℝ)
    (ma : ∀ i, AEStronglyMeasurable (a i) μ) (mt : ∀ i, AEStronglyMeasurable (t i) μ)
    (hc : ∀ i, 0 ≤ c i) (he : ∀ i, 0 ≤ e i)
    (actual : ∀ i, Integrable (fun z => ‖a i z‖ ^ Fintype.card I) μ ∧
      ∫ z, ‖a i z‖ ^ Fintype.card I ∂μ ≤ c i ^ Fintype.card I)
    (error : ∀ i, Integrable (fun z => ‖t i z - a i z‖ ^ Fintype.card I) μ ∧
      ∫ z, ‖t i z - a i z‖ ^ Fintype.card I ∂μ ≤ e i ^ Fintype.card I)
    {δ : ℝ} (d0 : 0 ≤ δ) (d1 : δ ≤ 1)
    (base : ∀ i, c i ≤ b i) (extra : ∀ i, e i ≤ δ * b i)
    (J : Ω → ℂ) (jm : AEStronglyMeasurable J μ) {B : ℝ} (b0 : 0 ≤ B)
    (bounded : ∀ z, ‖J z‖ ≤ B) :
    let defect := fun z => (∏ i, t i z) - ∏ i, a i z
    Integrable (fun z => J z * defect z) μ ∧
      ‖∫ z, J z * defect z ∂μ‖ ≤
        B * ((((Finset.univ : Finset (Finset I)).erase ∅).card : ℝ) * δ * ∏ i, b i) := by
  intro defect
  obtain ⟨int, bill⟩ := joined_vertex_errors μ a t c e ma mt hc he actual error
  have dom (z : Ω) : ‖J z * defect z‖ ≤ B * ‖defect z‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (bounded z) (norm_nonneg _)
  have full : Integrable (fun z => J z * defect z) μ :=
    (int.norm.const_mul B).mono' (jm.mul int.1) (Filter.Eventually.of_forall dom)
  refine ⟨full, (norm_integral_le_integral_norm _).trans ?_⟩
  calc
    _ ≤ ∫ z, B * ‖defect z‖ ∂μ :=
      integral_mono full.norm (int.norm.const_mul B) dom
    _ = B * ∫ z, ‖defect z‖ ∂μ := integral_const_mul B _
    _ ≤ _ := mul_le_mul_of_nonneg_left ((bill.trans (occupied_budget c e b d0 d1 hc he base extra))) b0

end YM.Integration.OriginalMarkedRunAction

