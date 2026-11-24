import YM.Integration.FVA1Physical.Marked.MeanLedger
import YM.Integration.FVA1Physical.Sources.AnchorProbability

/-! A local failed-flag invoice for incoming product errors. The conditional
probability can vary with the observed coarse field. Its exact average under
the same Wilson law is the fine flag probability with its period-uniform bound. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Filter Set MeasureTheory Lattice RG YM.Wilson OPE.Therm
open scoped BigOperators Classical
variable {G : Gauge} (A : History G) (selected : A.Selected) {N n m : ℕ} (hi : m < N)
local notation "Fine" => Config G (A.S.side (m+1) n)
local notation "Coarse" => Config G (A.S.side m n)
local notation "op" => A.levels.clock.op m n
local notation "β₀" => A.β N n (m+1)
local notation "source" => RG.Rep.eval (A.rep N n (m+1))
local notation "targetV" => RG.Rep.eval (A.rep N n m)
local notation "μ" => prior G (A.S.side (m+1) n)

include selected hi in
/-- An indicator propagated through the measured coarse kernel has the same
mean as the original fine indicator under the actual Wilson laws. -/
theorem posterior_event_mass (K : Set Fine) (hK : MeasurableSet K) :
    (∫ V, conditionalPush A N n m (K.indicator (fun _=> (1:ℝ))) V ∂scene A N n m) =
      (scene A N n (m+1)).real K := by
  let f := K.indicator (fun _ : Fine=>(1:ℝ))
  let z := partition G (A.S.side N n) (A.β N n N)
  have pos (V : Coarse) : 0 < targetV V := SectorNext.Vacuum.strictly A selected N n m hi.le V
  have start : Integrable source μ := ((A.rep N n (m+1)).envelope (selected.represents N n (m+1) hi).good).integrable _
  have mul : (fun u=>source u*f u) = K.indicator source := by
    funext u
    by_cases hu:u∈K <;> simp [f,hu]
  have endow : Integrable (fun u=>source u * f u) μ := by rw [mul]; exact start.indicator hK
  have clear (V) : targetV V * conditionalPush A N n m f V =
      (op).push β₀ (fun u=>source u*f u) V := by
    unfold conditionalPush
    simp only [smul_eq_mul,←mul_assoc,mul_inv_cancel₀ (pos V).ne',one_mul]
  calc
    _ = (∫ V,targetV V * conditionalPush A N n m f V ∂prior G (A.S.side m n))/z := scenery selected hi.le _
    _ = (∫ u,source u*f u ∂μ)/z := by
      simp_rw [clear]
      rw [StepData.push_integral (A.levels.transition_mass m n β₀) _ endow]
    _ = ∫ u,f u ∂scene A N n (m+1) := (scenery selected hi f).symm
    _ = _ := by simp [f,integral_indicator hK,measureReal_def]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
include selected hi in
/-- Bound the defect on the good sector by `small` and on its exceptional
complement by `small + excess`. Only the actual conditional probability of
this particular event multiplies `excess`. -/
theorem conditional_failure_price (K : Set Fine) (hK : MeasurableSet K) (F : Fine→E) (small excess : ℝ)
    (hgood : ∀ u∉K, ‖F u‖ ≤ small) (hbad : ∀ u∈K, ‖F u‖ ≤ small+excess) (V : Coarse) :
    ‖conditionalPush A N n m F V‖ ≤ small + excess * conditionalPush A N n m (K.indicator (fun _=>(1:ℝ))) V := by
  let kernel := A.levels.transition_mass m n β₀
  let w := fun u=>(op).density β₀ u V * source u
  let f := K.indicator (fun _ : Fine=>(1:ℝ))
  let Z := targetV V
  have hz : 0 < Z := SectorNext.Vacuum.strictly A selected N n m hi.le V
  have nh (u) : 0 ≤ w u := mul_nonneg (kernel.positive u V) (A.nonnegative selected N n (m+1) hi u)
  have int : Integrable w μ := StepData.push_slice kernel V _ (((A.rep N n (m+1)).envelope (selected.represents N n (m+1) hi).good).integrable _)
  have mask : (fun u=>w u*f u) = K.indicator w := by funext u; by_cases h:u∈K <;> simp [f,h]
  have it : Integrable (fun u=>w u*f u) μ := by rw [mask]; exact int.indicator hK
  have total : (∫ u,w u ∂μ) = Z := (congrFun (selected.steps N n m hi).1 V).symm
  have obs : ∀ u, ‖F u‖ ≤ small + f u*excess := by
    intro u
    by_cases hu:u∈K
    · simpa only [f,hu,Set.indicator_of_mem,one_mul] using hbad u hu
    · simpa [f, hu] using hgood u hu
  have num : ‖∫ u,w u • F u ∂μ‖ ≤ Z*small + (∫ u,w u*f u ∂μ)*excess := by
    rw [←total,← integral_mul_const,← integral_mul_const,← integral_add (int.mul_const small) (it.mul_const excess)]
    apply norm_integral_le_of_norm_le ((int.mul_const small).add (it.mul_const excess))
    filter_upwards with u
    rw [norm_smul,Real.norm_of_nonneg (nh u)]
    exact (mul_le_mul_of_nonneg_left (obs u) (nh u)).trans_eq (by change _ = w u * small + (w u * f u) * excess; ring)
  have oneField : conditionalPush A N n m F V = Z⁻¹ • (∫ u,w u • F u ∂μ) := by
    unfold conditionalPush StepData.push
    apply congrArg (Z⁻¹ • ·)
    exact integral_congr_ae (Eventually.of_forall fun u=>(smul_smul ((op).density β₀ u V) (source u) (F u)))
  have fra : conditionalPush A N n m f V = Z⁻¹ * (∫ u,w u*f u ∂μ) := by
    unfold conditionalPush StepData.push
    simp only [smul_eq_mul]
    apply congrArg (Z⁻¹ * ·)
    exact integral_congr_ae (Eventually.of_forall fun u=>(mul_assoc ((op).density β₀ u V) (source u) (f u)).symm)
  rw [oneField,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hz.le),fra]
  exact (mul_le_mul_of_nonneg_left num (inv_nonneg.mpr hz.le)).trans_eq (by field_simp [hz.ne'])

include selected in
/-- The paid exceptional conditional probability has period-independent
Wilson mean. Only the number of anchors and the physical flagged-face rate
appear. -/
theorem posterior_anchor_rarity (hP : Poetry A.levels) (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop, ∀ (N n : ℕ) (_ : m < N) (sites : Support (A.S.side (m+1) n)),
      let K := {u : Config G (A.S.side (m+1) n) | ¬ Healthy (A.rep N n (m+1)).p.threshold sites u}
      (∫ V, conditionalPush A N n m (K.indicator (fun _=>(1:ℝ))) V ∂scene A N n m) ≤
        ((sites.card * 5^4 * Fintype.card PlaqAxes : ℕ):ℝ) * vanishP A.levels (m+1) := by
  obtain ⟨m₀,long⟩ := eventually_atTop.1 (anchoredFlag_probability selected hP hG)
  filter_upwards [eventually_ge_atTop m₀] with m hm
  intro N n hi sites K
  rw [posterior_event_mass A selected hi K (healthy_closed _ sites).measurableSet.compl]
  exact long (m+1) (by omega) N n hi sites
end YM.Integration.FVA1Physical.Marked
