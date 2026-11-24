import YM.Integration.ActualNormalizedLocalDensity
import YM.Integration.LocalComparisonForcedMajorant

/-! Common positive coefficient majorants through the actual transition.

The test supremum remains inside every marked coefficient. The final
quantity is an explicit integral against the actual kernel and exponential
background, divided by the actual outgoing vacuum. No small bound on that
remaining forced-tail integral is assumed or inferred. These are value and
coefficient estimates, not a differentiated local representation norm.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.UniformPolynomialComparison
open Marker MeasureTheory Finset
open scoped BigOperators Classical

variable {V X Ω : Type*} [DecidableEq V] {R : Census V}
    [MeasurableSpace Ω] {μ : Measure Ω}

theorem Positive.smul {A : Poly R} (hA : Positive A) {c : ℝ} (hc : 0 ≤ c) :
    Positive (c • A) := by
  intro s
  change 0 ≤ ((c : ℂ) * A.part s).re ∧ ((c : ℂ) * A.part s).im = 0
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  exact ⟨mul_nonneg hc (hA s).1, by rw [(hA s).2, mul_zero]⟩

theorem Dominates.smul {A : Poly R} {F : X → Poly R}
    (hF : Dominates A F) {c : ℝ} (hc : 0 ≤ c) :
    Dominates (c • A) (fun x => c • F x) := by
  intro x s
  change ‖(c : ℂ) * (F x).part s‖ ≤ ((c : ℂ) * A.part s).re
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left (hF x s) hc

theorem Positive.integral {Q : Ω → Poly R} (hQ : Integrable Q μ)
    (hp : ∀ u, Positive (Q u)) : Positive (∫ u, Q u ∂μ) := by
  intro s
  let L : Poly R →L[ℝ] ℝ := Complex.reCLM.comp ((Poly.get s).restrictScalars ℝ)
  let K : Poly R →L[ℝ] ℝ := Complex.imCLM.comp ((Poly.get s).restrictScalars ℝ)
  change 0 ≤ L (∫ u, Q u ∂μ) ∧ K (∫ u, Q u ∂μ) = 0
  rw [← L.integral_comp_comm hQ, ← K.integral_comp_comm hQ]
  refine ⟨integral_nonneg (fun u => (hp u s).1), ?_⟩
  have hz : (fun u => K (Q u)) = fun _ => (0 : ℝ) := by
    funext u
    exact (hp u s).2
  rw [hz, integral_zero]

theorem Dominates.integral {Q : Ω → Poly R} {F : X → Ω → Poly R}
    (hQ : Integrable Q μ) (hF : ∀ x, Integrable (F x) μ)
    (hd : ∀ u, Dominates (Q u) (fun x => F x u)) :
    Dominates (∫ u, Q u ∂μ) (fun x => ∫ u, F x u ∂μ) := by
  intro x s
  let L : Poly R →L[ℝ] ℂ := (Poly.get s).restrictScalars ℝ
  let K : Poly R →L[ℝ] ℝ := Complex.reCLM.comp L
  change ‖L (∫ u, F x u ∂μ)‖ ≤ K (∫ u, Q u ∂μ)
  rw [← L.integral_comp_comm (hF x), ← K.integral_comp_comm hQ]
  exact norm_integral_le_of_norm_le (K.integrable_comp hQ)
    (ae_of_all _ fun u => hd u x s)

/-- On positive coefficient polynomials the price is a real linear map. -/
def priceLinear (w : V → ℝ) : Poly R →L[ℝ] ℝ :=
  ∑ s : R.Mode, Poly.toll w s •
    (Complex.reCLM.comp ((Poly.get s).restrictScalars ℝ))

theorem priceLinear_positive (w : V → ℝ) {A : Poly R} (hA : Positive A) :
    priceLinear w A = Poly.price w A := by
  simp only [priceLinear, _root_.sum_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', Poly.price, smul_eq_mul]
  apply sum_congr rfl
  intro s _
  rw [hA.norm]
  rfl

theorem positive_price_integrable (w : V → ℝ) {Q : Ω → Poly R}
    (hQ : Integrable Q μ) (hp : ∀ u, Positive (Q u)) :
    Integrable (fun u => Poly.price w (Q u)) μ := by
  have he : (fun u => Poly.price w (Q u)) = fun u => priceLinear w (Q u) := by
    funext u
    exact (priceLinear_positive w (hp u)).symm
  rw [he]
  exact (priceLinear w).integrable_comp hQ

theorem positive_price_integral (w : V → ℝ) {Q : Ω → Poly R}
    (hQ : Integrable Q μ) (hp : ∀ u, Positive (Q u)) :
    Poly.price w (∫ u, Q u ∂μ) = ∫ u, Poly.price w (Q u) ∂μ := by
  rw [← priceLinear_positive w (Positive.integral hQ hp),
    ← (priceLinear w).integral_comp_comm hQ]
  exact integral_congr_ae (ae_of_all _ fun u => priceLinear_positive w (hp u))

theorem price_real_smul (w : V → ℝ) (A : Poly R) {c : ℝ} (hc : 0 ≤ c) :
    Poly.price w (c • A) = c * Poly.price w A := by
  rw [← Complex.coe_smul, Poly.adapted, Complex.norm_real,
    Real.norm_of_nonneg hc]

variable [Fintype V]

theorem Positive.pass {A : Poly R} (hA : Positive A) : Positive (Poly.pass A) := by
  rw [pass_eq_one_add_tail]
  exact positive_one.add hA.tail

theorem Dominates.pass {A : Poly R} {F : X → Poly R}
    (hF : Dominates A F) (hA : Positive A) :
    Dominates (Poly.pass A) (fun x => Poly.pass (F x)) := by
  intro x s
  change ‖(Poly.pass (F x)).part s‖ ≤ ((Poly.pass A).part s).re
  rw [pass_eq_one_add_tail, pass_eq_one_add_tail, Poly.part_plus,
    Poly.part_plus, Complex.add_re]
  exact (norm_add_le _ _).trans
    (add_le_add (dominates_one (α := X) x s) (hF.tail hA x s))

end YM.Integration.UniformPolynomialComparison

namespace YM.Integration.ForcedNormalization
open Lattice Wilson RG Marker MeasureTheory Finset
open UniformPolynomialComparison LocalComparison
open scoped BigOperators Classical

variable {G : Gauge} {n : Side}

/-- Finite-volume boundedness is used only to justify the genuine integral. -/
theorem flag_function_envelope (t : ℝ) (b : Support n → ℝ) :
    Envelope (fun U : Config G n => b (flags t U)) := by
  have he : (fun U : Config G n => b (flags t U)) =
      fun U => ∑ s : Support n, if flags t U = s then b s else 0 := by
    funext U
    simp
  refine ⟨?_, ∑ s : Support n, ‖b s‖, fun U => ?_⟩
  · rw [he]
    exact Finset.measurable_fun_sum _ fun s _ =>
      Measurable.ite (flags_measurable_eq t s) measurable_const measurable_const
  exact single_le_sum (fun s _ => norm_nonneg (b s)) (mem_univ (flags t U))

def flagPrice (t γ M : ℝ) (U : Config G n) : ℝ :=
  if flags t U = ∅ then 0 else M * Real.exp (-γ * (flags t U).card)

theorem flagPrice_envelope (t γ M : ℝ) :
    Envelope (flagPrice (G := G) (n := n) t γ M) :=
  flag_function_envelope t (fun s => if s = ∅ then 0 else M * Real.exp (-γ * s.card))

variable {C : Family G} {N period level : ℕ}
    {V : Type} {X : Type*} [Fintype V] [DecidableEq V] {R : Census V}

/-- The actual positive kernel and outgoing vacuum preserve one common
coefficient majorant for all independently chosen test data. -/
theorem normalizedPush_majorant (hC : C.Makes) (hl : level < N)
    {B : Config G (C.side (level + 1) period) → Poly R}
    {F : X → Config G (C.side (level + 1) period) → Poly R}
    (hB : Integrable B (prior G _))
    (hF : ∀ x, Integrable (F x) (prior G _))
    (hp : ∀ U, Positive (B U))
    (hd : ∀ U, Dominates (B U) (fun x => F x U))
    (W : Config G (C.side level period)) :
    Positive (normalized C N period level (actualPush C N period level B) W) ∧
      Dominates (normalized C N period level (actualPush C N period level B) W)
        (fun x => normalized C N period level (actualPush C N period level (F x)) W) := by
  let K := C.path.levels.clock.op level period
  let β := C.path.β N period (level + 1)
  have hk := C.path.levels.transition_mass level period β
  have hInt := StepData.push_slice hk W B hB
  have hPos (U) := (hp U).smul (K.density_positive β U W)
  have hInv : 0 ≤ ((C.path.rep N period level).eval W)⁻¹ :=
    inv_nonneg.mpr (Multi.AxisShift.chosen_positive hC.wilson hl.le W).le
  constructor
  · simpa only [normalized, actualPush, StepData.push] using
      (Positive.integral hInt hPos).smul hInv
  simpa only [normalized, actualPush, StepData.push] using
    (Dominates.integral hInt (fun x => StepData.push_slice hk W (F x) (hF x))
      (fun U => (hd U).smul (K.density_positive β U W))).smul hInv

/-- The positive coefficient price commutes exactly with actual integration.
The denominator is the original full outgoing density. -/
theorem normalizedPush_price (hC : C.Makes) (hl : level < N) (w : V → ℝ)
    {B : Config G (C.side (level + 1) period) → Poly R}
    (hB : Integrable B (prior G _)) (hp : ∀ U, Positive (B U))
    (W : Config G (C.side level period)) :
    Poly.price w (normalized C N period level (actualPush C N period level B) W) =
      ((C.path.rep N period level).eval W)⁻¹ *
        (C.path.levels.clock.op level period).push (C.path.β N period (level + 1))
          (fun U => Poly.price w (B U)) W := by
  let K := C.path.levels.clock.op level period
  let β := C.path.β N period (level + 1)
  have hk := C.path.levels.transition_mass level period β
  have hInt := StepData.push_slice hk W B hB
  have hPos (U) := (hp U).smul (K.density_positive β U W)
  have hInv : 0 ≤ ((C.path.rep N period level).eval W)⁻¹ :=
    inv_nonneg.mpr (Multi.AxisShift.chosen_positive hC.wilson hl.le W).le
  change Poly.price w (((C.path.rep N period level).eval W)⁻¹ •
    ∫ U, K.density β U W • B U ∂prior G _) =
      ((C.path.rep N period level).eval W)⁻¹ *
        ∫ U, K.density β U W • Poly.price w (B U) ∂prior G _
  rw [price_real_smul w _ hInv, positive_price_integral w hInt hPos]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun U =>
    price_real_smul w (B U) (K.density_positive β U W))

theorem normalizedPush_price_le (hC : C.Makes) (hl : level < N) (w : V → ℝ)
    {B : Config G (C.side (level + 1) period) → Poly R}
    {g : Config G (C.side (level + 1) period) → ℝ}
    (hB : Integrable B (prior G _)) (hp : ∀ U, Positive (B U))
    (hg : Integrable g (prior G _)) (hb : ∀ U, Poly.price w (B U) ≤ g U)
    (W : Config G (C.side level period)) :
    Poly.price w (normalized C N period level (actualPush C N period level B) W) ≤
      ((C.path.rep N period level).eval W)⁻¹ *
        (C.path.levels.clock.op level period).push (C.path.β N period (level + 1)) g W := by
  rw [normalizedPush_price hC hl w hB hp]
  apply mul_le_mul_of_nonneg_left _
    (inv_nonneg.mpr (Multi.AxisShift.chosen_positive hC.wilson hl.le W).le)
  let K := C.path.levels.clock.op level period
  let β := C.path.β N period (level + 1)
  have hk := C.path.levels.transition_mass level period β
  exact integral_mono (StepData.push_slice hk W _ (positive_price_integrable w hB hp))
    (StepData.push_slice hk W g hg)
    (fun U => mul_le_mul_of_nonneg_left (hb U) (K.density_positive β U W))

end YM.Integration.ForcedNormalization

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker MeasureTheory Finset
open RG3.Forms RG3.Script.Picnic SectorNext.Vacuum
open UniformPolynomialComparison ForcedNormalization
open scoped BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
    {G : Gauge} {n : Side} {X : Type*} {P : Rep G n} {o : V → Site n}
    {T : Taste X o P R} {p : BudgetPoint} {w cost : V → ℝ}
    {κ regularPrice forcedPrice : ℝ}

/-- The native regular and forced suppliers combine before choosing any
test function. Every mixed marked term remains in the common polynomial.
The finite envelope is solely an integrability certificate. -/
theorem RelativeBudget.forced_numerator_majorant
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold) (x₀ : X)
    {σ A Λ δ k vacuum : ℝ} (hP : P.Lawful σ A Λ δ k)
    (hReserve : P.activities.KBound p vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1) :
    ∃ B : Config G n → Poly R, Envelope B ∧ ∀ U,
      Positive (B U) ∧
      Dominates (B U) (fun x => forcedNumerator (T.leaf x) U) ∧
      Poly.price (fun v => w v / cost v) (B U) ≤
        Real.exp (Fintype.card V * regularPrice) *
          (Real.exp (P.exponent U) * flagPrice P.p.threshold (flagRate p)
            (Fintype.card V * (κ * forcedPrice)) U) := by
  obtain ⟨A₀, hA, hLog, hPrice⟩ := h.physical_log_majorant hc x₀ ht
  obtain ⟨Q, hMeas, hQ⟩ := h.physical_forced_majorant hc x₀ hP.labels hReserve hSmall
  let B (U : Config G n) : Poly R :=
    Real.exp (P.exponent U) • (Poly.pass A₀ * Q U)
  have hw (v) : 0 < w v / cost v := div_pos (h.budget.radii v) (hc v)
  have hPass : Poly.price (fun v => w v / cost v) (Poly.pass A₀) ≤
      Real.exp (Fintype.card V * regularPrice) :=
    (Poly.pass_budget hw A₀).trans (Real.exp_monotone hPrice)
  have hp (U) : Positive (B U) :=
    (hA.pass.mul (hQ U).1).smul (Real.exp_pos _).le
  have hd (U) : Dominates (B U) (fun x => forcedNumerator (T.leaf x) U) := by
    have hl : Dominates A₀ (fun x => (T.leaf x).log U) := fun x s => hLog (x, U) s
    simpa only [B, forcedNumerator, Complex.coe_smul] using
      ((hl.pass hA).mul (hQ U).2.1 hA.pass (hQ U).1).smul (Real.exp_pos _).le
  have hb (U) : Poly.price (fun v => w v / cost v) (B U) ≤
      Real.exp (Fintype.card V * regularPrice) *
        (Real.exp (P.exponent U) * flagPrice P.p.threshold (flagRate p)
          (Fintype.card V * (κ * forcedPrice)) U) := by
    dsimp only [B]
    rw [price_real_smul _ _ (Real.exp_pos _).le]
    apply (mul_le_mul_of_nonneg_left
      ((Poly.multiplication hw _ _).trans
        (mul_le_mul hPass (hQ U).2.2 (Poly.nonnegative hw _) (Real.exp_pos _).le))
      (Real.exp_pos _).le).trans_eq
    unfold flagPrice
    ring
  refine ⟨B, ?_, fun U => ⟨hp U, hd U, hb U⟩⟩
  have hScalar := (Envelope.const (Real.exp (Fintype.card V * regularPrice))).mul
    ((P.exponentEnv hP).exp.mul
      (flagPrice_envelope P.p.threshold (flagRate p) (Fintype.card V * (κ * forcedPrice))))
  obtain ⟨b, hScalarBound⟩ := hScalar.cost
  obtain ⟨a, ha, hNorm⟩ := Poly.equivalent_norm (R := R) hw
  refine ⟨(P.exponentEnv hP).exp.meas.smul (measurable_const.mul hMeas), b * a, ?_⟩
  intro U
  exact (hNorm _).trans (mul_le_mul_of_nonneg_right
    ((hb U).trans ((Real.le_norm_self _).trans (hScalarBound U))) ha)

end YM.Integration.LocalComparison

namespace YM.Integration.ForcedNormalization
open Lattice Wilson RG Marker MeasureTheory
open LocalComparison UniformPolynomialComparison SectorNext.Vacuum
open RG3.Forms RG3.Script.Picnic
open scoped BigOperators Classical

variable {G : Gauge} (C : Family G) (N period level : ℕ)

/-- The actual remaining scalar bill. Its smallness is a separate analytic
question; no gas denominator is cancelled by an unrelated probability law. -/
def actualFlagTail (p : BudgetPoint) (M : ℝ) (W : Config G (C.side level period)) : ℝ :=
  ((C.path.rep N period level).eval W)⁻¹ *
    (C.path.levels.clock.op level period).push (C.path.β N period (level + 1))
      (fun U => Real.exp ((C.path.rep N period (level + 1)).exponent U) *
        flagPrice (C.path.rep N period (level + 1)).p.threshold (flagRate p) M U) W

variable {C N period level}
    {V : Type} [Fintype V] [DecidableEq V] {R : Census V} {X : Type*}
    {o : V → Site (C.side (level + 1) period)}
    {T : Taste X o (C.path.rep N period (level + 1)) R}
    {p : BudgetPoint} {w cost : V → ℝ} {κ regularPrice forcedPrice vacuum : ℝ}

/-- Native common-majorant integration with the independent-test supremum
inside each coefficient. The right side is the literal normalized flagged
tail, not an assumed volume-uniform error estimate. -/
theorem actualForcedDensityError_majorant (hC : C.Makes) (hl : level < N)
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v)
    (ht : p.threshold = (C.path.rep N period (level + 1)).p.threshold) (x₀ : X)
    (hReserve : (C.path.rep N period (level + 1)).activities.KBound p vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (W : Config G (C.side level period)) :
    ∃ Q : Poly R, Positive Q ∧
      Dominates Q (fun x : X => actualForcedDensityError T x W) ∧
      Poly.price (fun v => w v / cost v) Q ≤
        Real.exp (Fintype.card V * regularPrice) *
          actualFlagTail C N period level p (Fintype.card V * (κ * forcedPrice)) W := by
  let P := C.path.rep N period (level + 1)
  let K := C.path.levels.clock.op level period
  let β := C.path.β N period (level + 1)
  let E := Real.exp (Fintype.card V * regularPrice)
  let g (U : Config G (C.side (level + 1) period)) : ℝ :=
    Real.exp (P.exponent U) *
      flagPrice P.p.threshold (flagRate p) (Fintype.card V * (κ * forcedPrice)) U
  have hP := (hC.wilson.represents N period (level + 1) hl).good
  obtain ⟨B, hEnv, hB⟩ := h.forced_numerator_majorant hc ht x₀ hP hReserve hSmall
  have hInt := Push.SectorMeasure.Env.integrableX hEnv (prior G _)
  obtain ⟨hPos, hDom⟩ := normalizedPush_majorant hC hl hInt
    (fun x => h.forced_numerator_integrable hc ht hP x)
    (fun U => (hB U).1) (fun U => (hB U).2.1) W
  have hg : Integrable g (prior G _) :=
    ((P.exponentEnv hP).exp.mul
      (flagPrice_envelope P.p.threshold (flagRate p) (Fintype.card V * (κ * forcedPrice)))).integrable _
  refine ⟨normalized C N period level (actualPush C N period level B) W, hPos, hDom, ?_⟩
  apply (normalizedPush_price_le hC hl (fun v => w v / cost v) hInt
    (fun U => (hB U).1) (hg.const_mul E) (fun U => (hB U).2.2) W).trans_eq
  have he : K.push β (fun U => E * g U) W = E * K.push β g W := by
    unfold StepData.push
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun U => by simp only [smul_eq_mul]; ring
  change ((C.path.rep N period level).eval W)⁻¹ * K.push β (fun U => E * g U) W =
    E * (((C.path.rep N period level).eval W)⁻¹ * K.push β g W)
  rw [he]
  ring

/-- Independent-test uniformity after the actual normalized integration. -/
theorem actualForcedDensityError_uniform_price (hC : C.Makes) (hl : level < N)
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v)
    (ht : p.threshold = (C.path.rep N period (level + 1)).p.threshold) (x₀ : X)
    (hReserve : (C.path.rep N period (level + 1)).activities.KBound p vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (W : Config G (C.side level period)) :
    uniformPrice (fun v => w v / cost v) (fun x : X => actualForcedDensityError T x W) ≤
      Real.exp (Fintype.card V * regularPrice) *
        actualFlagTail C N period level p (Fintype.card V * (κ * forcedPrice)) W := by
  obtain ⟨Q, hp, hd, hb⟩ :=
    actualForcedDensityError_majorant hC hl h hc ht x₀ hReserve hSmall W
  exact (uniformPrice_le hp hd (fun v => div_pos (h.budget.radii v) (hc v))).trans hb

/-- Complete normalized local error, with the regular part paid by the
native rooted budget and the full mixed forced part by its literal tail
integral. No integral smallness or inverse-vacuum bound is postulated. -/
theorem actualLocalDensityError_uniform_price (hC : C.Makes) (hl : level < N)
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v)
    (ht : p.threshold = (C.path.rep N period (level + 1)).p.threshold) (x₀ : X)
    (hReserve : (C.path.rep N period (level + 1)).activities.KBound p vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (W : Config G (C.side level period)) :
    uniformPrice (fun v => w v / cost v) (fun x : X => actualLocalDensityError T x W) ≤
      (Real.exp (Fintype.card V * regularPrice) - 1) +
        Real.exp (Fintype.card V * regularPrice) *
          actualFlagTail C N period level p (Fintype.card V * (κ * forcedPrice)) W := by
  obtain ⟨A, hA, hLog, hPrice⟩ := h.physical_log_majorant hc x₀ ht
  obtain ⟨Q, hQ, hForce, hCost⟩ :=
    actualForcedDensityError_majorant hC hl h hc ht x₀ hReserve hSmall W
  have hReg : Dominates (tail A)
      (fun x : X => EngineeringWeightedReadout.actualRegularRemainder T x W) := by
    intro x s
    apply actualAverage_norm_le C hC hl
    intro U
    simpa only [pass_eq_one_add_tail, add_sub_cancel_left] using (hLog.tail hA) (x, U) s
  have hAll : Dominates (tail A + Q) (fun x : X => actualLocalDensityError T x W) := by
    intro x s
    change ‖(actualLocalDensityError T x W).part s‖ ≤ ((tail A + Q).part s).re
    rw [actualLocalDensityError_split hC hl h hc ht, Poly.part_plus,
      Poly.part_plus, Complex.add_re]
    exact (norm_add_le _ _).trans (add_le_add (hReg x s) (hForce x s))
  apply (uniformPrice_le (hA.tail.add hQ) hAll
    (fun v => div_pos (h.budget.radii v) (hc v))).trans
  rw [positive_price_add hA.tail hQ]
  exact add_le_add
    ((tail_price_le hA (fun v => div_pos (h.budget.radii v) (hc v))).trans
      (sub_le_sub_right (Real.exp_monotone hPrice) 1)) hCost

end YM.Integration.ForcedNormalization
