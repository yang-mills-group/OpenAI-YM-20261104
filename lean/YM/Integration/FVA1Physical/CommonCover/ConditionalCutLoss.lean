import YM.Integration.FVA1Physical.CommonCover.CenteredConditionalRead

/-! Remove a regular-chart restriction from a normalized conditional reading.
The price is the conditional probability of the omitted configurations on
each of the two original laws. No lower bound on the mass of the retained
region is needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.FrozenRead
open MeasureTheory RG Set Filter
open scoped Classical
open private subtract_const from YM.Integration.FVA1Physical.CommonCover.CenteredConditionalRead
variable {X : Type*} [MeasurableSpace X]

def meanOn (μ : Measure X) (a : X → ℝ) (F : X → ℂ) : ℂ :=
  (∫ x, a x ∂μ)⁻¹ • (∫ x, a x • F x ∂μ)

private theorem numerator_price (μ : Measure X) {a : X → ℝ} (ia : Integrable a μ)
    (an : ∀ x, 0 ≤ a x) {F : X → ℂ} {M : ℝ} (bound : ∀ x, ‖F x‖ ≤ M) :
    ‖∫ x, a x • F x ∂μ‖ ≤ (∫ x, a x ∂μ)*M := by
  rw [←integral_mul_const]
  apply norm_integral_le_of_norm_le (ia.mul_const M)
  filter_upwards with x
  rw [norm_smul,Real.norm_of_nonneg (an _)]
  exact mul_le_mul_of_nonneg_left (bound x) (an x)

theorem restore_one_cut (μ : Measure X) {a : X → ℝ} (ia : Integrable a μ)
    (an : ∀ x, 0 ≤ a x) (total : 0 < ∫ x, a x ∂μ) {E : Set X} (em : MeasurableSet E)
    {F : X → ℂ} (fm : Measurable F) {M : ℝ} (mp : 0 ≤ M) (bound : ∀ x, ‖F x‖ ≤ M) :
    ‖meanOn μ a F - meanOn (μ.restrict E) a F‖ ≤
      2*M*((∫ x in Eᶜ, a x ∂μ)/(∫ x, a x ∂μ)) := by
  let good := ∫ x in E, a x ∂μ
  let bad := ∫ x in Eᶜ, a x ∂μ
  let all := ∫ x, a x ∂μ
  let r := meanOn (μ.restrict E) a F
  let s := fun x => a x • F x
  have si : Integrable s μ := by
    apply (ia.norm.mul_const M).mono' (ia.aestronglyMeasurable.smul fm.aestronglyMeasurable)
    filter_upwards with x
    exact (norm_smul (a x) (F x)).le.trans (mul_le_mul_of_nonneg_left (bound x) (norm_nonneg _))
  have gp : 0 ≤ good := integral_nonneg an
  have bp : 0 ≤ bad := integral_nonneg an
  have gn : ‖∫ x in E, s x ∂μ‖ ≤ good*M := numerator_price _ ia.integrableOn an bound
  have bn : ‖∫ x in Eᶜ, s x ∂μ‖ ≤ bad*M := numerator_price _ ia.integrableOn an bound
  have gr : good • r = ∫ x in E, s x ∂μ := by
    by_cases z : good=0
    · have t : ‖∫ x in E, s x ∂μ‖ ≤ 0 := by simpa only [z,zero_mul] using gn
      rw [z,zero_smul,norm_le_zero_iff.mp t]
    change good • (good⁻¹ • _) = _
    rw [smul_smul,mul_inv_cancel₀ z,one_smul]
  have rb : ‖r‖ ≤ M := by
    change ‖good⁻¹ • _‖ ≤ M
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr gp)]
    by_cases z : good=0
    · simpa only [z,inv_zero,zero_mul] using mp
    exact (mul_le_mul_of_nonneg_left gn (inv_nonneg.mpr gp)).trans_eq (by rw [←mul_assoc,inv_mul_cancel₀ z,one_mul])
  have ar : all • meanOn μ a F = ∫ x, s x ∂μ := by
    change all • (all⁻¹ • _) = _
    rw [smul_smul,mul_inv_cancel₀ total.ne',one_smul]
  have splitMass : good+bad=all := integral_add_compl em ia
  have splitRow : (∫ x in E, s x ∂μ)+(∫ x in Eᶜ, s x ∂μ)=∫ x, s x ∂μ := integral_add_compl em si
  have eqn : all • (meanOn μ a F-r) = (∫ x in Eᶜ, s x ∂μ)-bad • r := by
    rw [smul_sub,ar,←splitRow,←splitMass,add_smul,gr]
    abel
  have tail : ‖bad • r‖ ≤ bad*M := by
    rw [norm_smul,Real.norm_of_nonneg bp]
    exact mul_le_mul_of_nonneg_left rb bp
  have cap := (norm_sub_le (∫ x in Eᶜ, s x ∂μ) (bad • r)).trans (add_le_add bn tail)
  rw [←eqn,norm_smul,Real.norm_of_nonneg total.le] at cap
  change _ ≤ 2*M*(bad/all)
  rw [←mul_div_assoc]
  exact (le_div_iff₀ total).mpr ((mul_comm ..).trans_le (cap.trans_eq (by ring)))

/-- The two missing masses are measured against their respective original
vacua. Different total normalizations and even zero retained mass are allowed. -/
theorem restore_two_cuts (μ : Measure X) {a b : X → ℝ} (ia : Integrable a μ) (ib : Integrable b μ)
    (an : ∀ x, 0 ≤ a x) (bn : ∀ x, 0 ≤ b x) (am : 0 < ∫ x, a x ∂μ) (bm : 0 < ∫ x, b x ∂μ)
    {E : Set X} (em : MeasurableSet E) {F : X → ℂ} (fm : Measurable F) {M δ : ℝ}
    (mp : 0 ≤ M) (bound : ∀ x, ‖F x‖ ≤ M)
    (chart : ‖meanOn (μ.restrict E) a F-meanOn (μ.restrict E) b F‖ ≤ δ*M) :
    ‖meanOn μ a F-meanOn μ b F‖ ≤ (δ+2*((∫ x in Eᶜ,a x ∂μ)/(∫ x,a x ∂μ)+
      (∫ x in Eᶜ,b x ∂μ)/(∫ x,b x ∂μ)))*M := by
  let A := meanOn μ a F
  let B := meanOn μ b F
  let X₁ := meanOn (μ.restrict E) a F
  let X₂ := meanOn (μ.restrict E) b F
  have ta := restore_one_cut μ ia an am em fm mp bound
  have tb := restore_one_cut μ ib bn bm em fm mp bound
  have triangle : ‖A-B‖ ≤ ‖A-X₁‖ + ‖X₁-X₂‖ + ‖B-X₂‖ := by
    calc
      _ = ‖((A-X₁)+(X₁-X₂))-(B-X₂)‖ := by congr 1; abel
      _ ≤ _ := (norm_sub_le ..).trans (add_le_add (norm_add_le ..) le_rfl)
  exact triangle.trans ((add_le_add (add_le_add ta chart) tb).trans_eq (by ring))

theorem restore_centered_roster {J : Type*} (μ : Measure X) {a b : X → ℝ}
    (ia : Integrable a μ) (ib : Integrable b μ) (an : ∀ x, 0 ≤ a x) (bn : ∀ x, 0 ≤ b x)
    (am : 0 < ∫ x, a x ∂μ) (bm : 0 < ∫ x, b x ∂μ) {E : Set X} (em : MeasurableSet E) (δ : ℝ)
    (chart : ∀ T : X → ℂ, Envelope T → ∀ M : ℝ, 0 ≤ M → (∀ x, ‖T x‖ ≤ M) →
      ‖meanOn (μ.restrict E) a T - meanOn (μ.restrict E) b T‖ ≤ δ*M)
    (w : J → ℝ) (wn : ∀ i, 0 ≤ w i) (F : J → X → ℂ) (env : ∀ i, Envelope (F i))
    (c : J → ℂ) (M : ℝ) (mp : 0 ≤ M) (osc : ∀ x (s : Finset J), ∑ i ∈ s, w i*‖F i x-c i‖ ≤ M) :
    let fees := fun i => w i*‖meanOn μ a (F i)-meanOn μ b (F i)‖
    Summable fees ∧ ∑' i, fees i ≤ (δ+2*((∫ x in Eᶜ,a x ∂μ)/(∫ x,a x ∂μ)+
      (∫ x in Eᶜ,b x ∂μ)/(∫ x,b x ∂μ)))*M := by
  intro fees
  let offset := fun i x => F i x-c i
  have shifted (i) : Envelope (offset i) := by
    obtain ⟨C,h⟩ := (env i).cost
    exact ⟨(env i).meas.sub measurable_const,C+‖c i‖,fun x => (norm_sub_le ..).trans (add_le_add (h x) le_rfl)⟩
  have same (i) : meanOn μ a (offset i)-meanOn μ b (offset i) = meanOn μ a (F i)-meanOn μ b (F i) := by
    unfold meanOn
    rw [subtract_const μ a (F i) (env i) (c i),subtract_const μ b (F i) (env i) (c i),
      if_neg am.ne',if_neg bm.ne']
    abel
  have read := summable_conditional_read μ a b _ (fun T ht B bp hb =>
    restore_two_cuts μ ia ib an bn am bm em ht.meas bp hb (chart T ht B bp hb)) w wn offset shifted M mp osc
  change Summable (fun i => w i*‖meanOn μ a (offset i)-meanOn μ b (offset i)‖) ∧
    (∑' i, w i*‖meanOn μ a (offset i)-meanOn μ b (offset i)‖) ≤ _ at read
  simpa only [fees,same] using read

private theorem meanOn_cut (μ : Measure X) (a : X → ℝ) {E : Set X} (em : MeasurableSet E)
    (T : X → ℂ) : meanOn μ (E.indicator a) T = meanOn (μ.restrict E) a T := by
  have num : (fun x => E.indicator a x • T x) = E.indicator (fun x => a x • T x) := by
    funext x
    by_cases member : x ∈ E <;> simp [Set.indicator, member]
  simp only [meanOn,num,integral_indicator em]

/-- Restore the original full law, keeping the comparison law on its proven chart.
The observable is anchored at an exterior-dependent constant on an empty chart.
Only the original conditional mass of the omitted set appears. -/
theorem restore_anchored_roster {J : Type*} (μ : Measure X) {a b : X → ℝ}
    (ia : Integrable a μ) (an : ∀ x, 0 ≤ a x) (am : 0 < ∫ x, a x ∂μ)
    {E : Set X} (em : MeasurableSet E) (δ : ℝ)
    (chart : ∀ T : X → ℂ, Envelope T → ∀ M : ℝ, 0 ≤ M → (∀ x, ‖T x‖ ≤ M) →
      ‖meanOn (μ.restrict E) a T-meanOn (μ.restrict E) b T‖ ≤ δ*M)
    (w : J → ℝ) (wn : ∀ i, 0 ≤ w i) (F : J → X → ℂ) (env : ∀ i, Envelope (F i))
    (c : J → ℂ) (M : ℝ) (mp : 0 ≤ M) (osc : ∀ x (s : Finset J), ∑ i ∈ s, w i*‖F i x-c i‖ ≤ M) :
    let fees := fun i => w i*‖meanOn μ a (F i) -
      (c i + meanOn (μ.restrict E) b (fun x => F i x-c i))‖
    Summable fees ∧ ∑' i, fees i ≤ (δ+2*((∫ x in Eᶜ,a x ∂μ)/(∫ x,a x ∂μ)))*M := by
  intro fees
  let offset := fun i x => F i x-c i
  have shifted (i) : Envelope (offset i) := by
    obtain ⟨C,h⟩ := (env i).cost
    exact ⟨(env i).meas.sub measurable_const,C+‖c i‖,fun x => (norm_sub_le ..).trans (add_le_add (h x) le_rfl)⟩
  have quote (i) : meanOn μ a (offset i)-meanOn μ (E.indicator b) (offset i) =
      meanOn μ a (F i)-(c i+meanOn (μ.restrict E) b (offset i)) := by
    rw [meanOn_cut μ b em]
    unfold meanOn
    rw [subtract_const μ a (F i) (env i) (c i),if_neg am.ne']
    abel
  have read := summable_conditional_read μ a (E.indicator b)
    (δ+2*((∫ x in Eᶜ,a x ∂μ)/(∫ x,a x ∂μ))) (fun T ht B bp bound => by
      change ‖meanOn μ a T-meanOn μ (E.indicator b) T‖ ≤ _
      rw [meanOn_cut μ b em]
      exact (norm_sub_le_norm_sub_add_norm_sub _ (meanOn (μ.restrict E) a T) _).trans
        ((add_le_add (restore_one_cut μ ia an am em ht.meas bp bound) (chart T ht B bp bound)).trans_eq (by ring)))
    w wn offset shifted M mp osc
  change Summable (fun i => w i*‖meanOn μ a (offset i)-meanOn μ (E.indicator b) (offset i)‖) ∧
    (∑' i, w i*‖meanOn μ a (offset i)-meanOn μ (E.indicator b) (offset i)‖) ≤ _ at read
  simpa only [fees,quote,offset] using read

end YM.Integration.FVA1Physical.FrozenRead
