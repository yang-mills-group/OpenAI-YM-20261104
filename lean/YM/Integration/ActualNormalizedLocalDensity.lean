/- The finite-family estimate in FullBudget.cluster_price uses the powerset-of-the-union argument
also given in `summable_finsetProd_of_summable_nonneg`.
Upstream source: Mathlib/Analysis/SpecialFunctions/Log/Summable.lean
Authors: Chris Birkbeck. Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache License 2.0. See NOTICE. -/

import YM.Integration.EngineeringWeightedReadout
import YM.Integration.LocalComparisonEnvelopeDensity
import YM.Push.SECTOR_MEASURE.Decompose

/-! Integrability and exact normalization of the full native marked density.

The absolute gas bound below is deliberately a finite-volume bound. It is
used to justify genuine integrals and their linearity, never as a uniform
small forced-error estimate. The regular/forced decomposition keeps the
original representation, transition, full vacuum, and every marked term.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker Finset Overlay RG3.Forms RG3.Script.Picnic
open MeasureTheory Filter
open scoped BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
    {G : Gauge} {n : Side} {X : Type*} {P : Rep G n} {o : V → Site n}
    {T : Taste X o P R} {p : BudgetPoint} {w : V → ℝ}
    {κ regularPrice forcedPrice : ℝ}

/-- The full marked forced family is absolutely summable at fixed volume.
Its extensive unmarked cost is displayed, rather than absorbed into a
purported volume-uniform small-error bound. -/
theorem FullBudget.each_price
    (h : FullBudget p T w κ regularPrice forcedPrice)
    {δ k : ℝ} (hP : P.activities.Valid P.p δ k) (x : X) (U : Config G n) :
    SumBudget (fun i => Poly.price w ((T.leaf x).contents.each i U))
      (Fintype.card (Site n) * k + Fintype.card V * (κ * forcedPrice)) := by
  let a := (T.leaf x).contents
  obtain ⟨q, hq, hroot⟩ := hP.boundK
  have hs (i) : (P.activities.forced i).support.Nonempty :=
    (P.activities.forced i).inventory_ne.mono (P.activities.forced i).inventory_sup
  have hqsum : Summable q := Activities.summable_charge hs (fun i => (hq i).1) hroot
  have hqprice := sumRoot hs (fun i => (hq i).1) hroot
  let b (i : ℕ × ℕ) := Poly.toll w (a.marks i.1 i.2) *
    p.mass (P.activities.forced i.1).support (h.black i)
  have hb : SumBudget b (Fintype.card V * (κ * forcedPrice)) :=
    per_system
      (fun i => mul_nonneg (Poly.worth h.radii _).le
        ((h.black_nonnegative i).trans (p.loMass _ _ (h.black_nonnegative i))))
      (P := fun i : ℕ × ℕ => a.marks i.1 i.2)
      (fun i => (h.active x).articles.occurs i.1 i.2) h.forcedTotal
  obtain ⟨hrow, hsum⟩ := (summable_prod_of_nonneg (show 0 ≤ b from hb.1)).mp hb.2.1
  let c (i : ℕ) := ∑' j, b (i, j)
  have hc (i) : Poly.price w (∑' j, a.tagged i j U) ≤ c i := by
    apply (Poly.budgeted h.radii (hrow i) ?_).2
    intro j
    rw [Bands.tagged, Poly.solo]
    exact mul_le_mul_of_nonneg_left
      ((h.forced x i j U).trans (p.loMass _ _ (h.black_nonnegative (i, j))))
      (Poly.worth h.radii _).le
  have he (i) : Poly.price w (a.each i U) ≤ q i + c i := by
    rw [Bands.each]
    apply (Poly.addition h.radii _ _).trans (add_le_add ?_ (hc i))
    simpa only [Poly.solo, Poly.quiet_toll, Complex.norm_real, one_mul] using (hq i).2 U
  have hall := hqsum.add hsum
  have hi := hall.of_nonneg_of_le (fun i => Poly.nonnegative h.radii _) he
  refine ⟨fun i => Poly.nonnegative h.radii _, hi, (hi.tsum_le_tsum he hall).trans ?_⟩
  rw [Summable.tsum_add hqsum (f := q) (g := c) (show Summable c from hsum)]
  exact add_le_add hqprice ((hb.2.1.tsum_prod).symm.trans_le hb.2.2)

/-- Native absolute gas summation at fixed volume, using every forced slot.
No independence of marks, tests or compulsory-cover events is assumed. -/
theorem FullBudget.cluster_price
    (h : FullBudget p T w κ regularPrice forcedPrice)
    {δ k : ℝ} (hP : P.activities.Valid P.p δ k) (x : X) (U : Config G n) :
    Poly.price w ((T.leaf x).contents.cluster U) ≤
      Real.exp (Fintype.card (Site n) * k + Fintype.card V * (κ * forcedPrice)) := by
  let a := (T.leaf x).contents
  obtain ⟨hn, hs, hb⟩ := h.each_price hP x U
  let f (i : ℕ) := Poly.price w (a.each i U)
  have hprod : Summable (fun s : Finset ℕ => ∏ i ∈ s, f i) :=
    summable_finsetProd_of_summable_nonneg hn hs
  have hpacket (s : Finset ℕ) : Poly.price w (a.packet s U) ≤ ∏ i ∈ s, f i := by
    unfold Bands.packet
    split
    · exact Poly.multiple h.radii _ _
    rw [Poly.zero_price]
    exact prod_nonneg fun i _ => hn i
  apply (Poly.budgeted h.radii hprod hpacket).2.trans
  apply le_of_tendsto hprod.hasSum
  apply Eventually.of_forall
  intro s
  let all := s.biUnion id
  calc
    _ ≤ ∑ z ∈ all.powerset, ∏ i ∈ z, f i :=
      sum_le_sum_of_subset_of_nonneg
        (fun z hz => mem_powerset.mpr fun i hi => mem_biUnion.mpr ⟨z, hz, hi⟩)
        (fun z _ _ => prod_nonneg fun i _ => hn i)
    _ = ∏ i ∈ all, (1 + f i) := (Finset.prod_one_add all).symm
    _ ≤ ∏ i ∈ all, Real.exp (f i) :=
      prod_le_prod (fun i _ => add_nonneg zero_le_one (hn i))
        (fun i _ => (add_comm (1 : ℝ) (f i)).le.trans (Real.add_one_le_exp (f i)))
    _ = Real.exp (∑ i ∈ all, f i) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_monotone ((hs.sum_le_tsum _ fun i _ => hn i).trans hb)

variable {cost : V → ℝ}

/-- The unmodified physical density has a finite absolute price; the
extensive gas constant remains explicit. This is only an integrability bill. -/
theorem RelativeBudget.full_density_price
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    {δ k : ℝ} (hP : P.activities.Valid P.p δ k) (x : X) (U : Config G n) :
    Poly.price (fun v => w v / cost v) ((T.leaf x).density U) ≤
      Real.exp (P.exponent U + Fintype.card V * regularPrice +
        (Fintype.card (Site n) * k + Fintype.card V * (κ * forcedPrice))) := by
  rw [density_product_price T cost hc w x U]
  let d := ((priceNormalized (envelopeProduct cost) T).leaf x)
  change Poly.price w ((Real.exp (P.exponent U) : ℂ) •
    (Poly.pass (d.log U) * d.contents.cluster U)) ≤ _
  rw [Poly.adapted, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ Real.exp (P.exponent U) *
        (Real.exp (Fintype.card V * regularPrice) *
          Real.exp (Fintype.card (Site n) * k + Fintype.card V * (κ * forcedPrice))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact (Poly.multiplication h.budget.radii _ _).trans
        (mul_le_mul (h.budget.pass_log_price ht x U) (h.budget.cluster_price hP x U)
          (Poly.nonnegative h.budget.radii _) (Real.exp_pos _).le)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- Envelope restoration also restores measurability of the full density. -/
theorem RelativeBudget.full_density_measurable
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) {σ A Λ δ k : ℝ}
    (hP : P.Lawful σ A Λ δ k) (x : X) : Measurable (T.leaf x).density := by
  have hn := ((priceNormalized (envelopeProduct cost) T).leaf x).density_read
    (h.budget.active x) hP
  simpa only [Function.comp_def, restoreEnvelope_density T cost hc x] using
    (restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)).continuous.measurable.comp hn

/-- All marked coefficients are integrable at each actual finite regulator.
The extensive constant is used here and nowhere to claim uniform smallness. -/
theorem RelativeBudget.full_density_envelope
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    {σ A Λ δ k : ℝ} (hP : P.Lawful σ A Λ δ k) (x : X) :
    Envelope (T.leaf x).density := by
  obtain ⟨b, hb⟩ := (P.exponentEnv hP).cost
  obtain ⟨a, ha, hprice⟩ := Poly.equivalent_norm (R := R)
    (fun v => div_pos (h.budget.radii v) (hc v))
  refine ⟨h.full_density_measurable hc hP x,
    Real.exp (b + Fintype.card V * regularPrice +
      (Fintype.card (Site n) * k + Fintype.card V * (κ * forcedPrice))) * a, ?_⟩
  intro U
  apply (hprice _).trans
  apply mul_le_mul_of_nonneg_right _ ha
  apply (h.full_density_price hc ht hP.labels x U).trans
  apply Real.exp_monotone
  have hu : P.exponent U ≤ b := (le_abs_self _).trans (hb U)
  linarith

/-- A finite bound for the actual regular polynomial, used only to justify
integration. The sharper uniform coefficient price remains available above. -/
theorem RelativeBudget.pass_log_envelope
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold) (x : X) :
    Envelope (fun U => Poly.pass ((T.leaf x).log U)) := by
  obtain ⟨a, ha, hprice⟩ := Poly.equivalent_norm (R := R)
    (fun v => div_pos (h.budget.radii v) (hc v))
  refine ⟨Poly.pass_cont.measurable.comp
    (EngineeringWeightedReadout.regular_log_measurable h x),
    Real.exp (Fintype.card V * regularPrice) * a, ?_⟩
  intro U
  apply (hprice _).trans
  apply mul_le_mul_of_nonneg_right _ ha
  have he : restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)
      (Poly.pass (((priceNormalized (envelopeProduct cost) T).leaf x).log U)) =
      Poly.pass ((T.leaf x).log U) := by
    rw [restoreEnvelope_product_pass cost hc,
      restoreEnvelope_log T (envelopeProduct cost) (envelopeProduct_positive hc)]
  rw [← he, restoreEnvelope_product_price cost w hc]
  exact h.budget.pass_log_price ht x U

theorem RelativeBudget.regular_error_envelope
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold) (x : X) :
    Envelope (fun U => Poly.pass ((T.leaf x).log U) - 1) := by
  have hp := h.pass_log_envelope hc ht x
  obtain ⟨b, hb⟩ := hp.cost
  exact ⟨hp.meas.sub measurable_const, b + ‖(1 : Poly R)‖,
    fun U => (norm_sub_le _ _).trans (add_le_add (hb U) le_rfl)⟩

omit [Fintype V] in
private theorem poly_integrable_of_envelope {f : Config G n → Poly R}
    (h : Envelope f) : Integrable f (prior G n) := by
  obtain ⟨b, hb⟩ := h.cost
  exact Integrable.of_bound h.meas.aestronglyMeasurable b (Eventually.of_forall hb)

/-- The complete forced error before normalization. The actual exponent and
every mixed regular/forced product remain in the numerator. -/
def forcedNumerator (d : Deck R P) (U : Config G n) : Poly R :=
  (Real.exp (P.exponent U) : ℂ) •
    (Poly.pass (d.log U) * forcedClusterError d U)

theorem forcedNumerator_eq_difference (d : Deck R P) (U : Config G n) :
    forcedNumerator d U = d.density U -
      (P.eval U : ℂ) • Poly.pass (d.log U) := by
  have h := density_error_split d U
  rw [smul_sub] at h
  apply (eq_sub_iff_add_eq).mpr
  calc
    _ = ((P.eval U : ℂ) • Poly.pass (d.log U) - (P.eval U : ℂ) • 1 +
      forcedNumerator d U) + (P.eval U : ℂ) • 1 := by abel
    _ = (d.density U - (P.eval U : ℂ) • 1) + (P.eval U : ℂ) • 1 := by
      rw [forcedNumerator, ← h]
    _ = d.density U := sub_add_cancel _ _

/-- Genuine finite-regulator integrability of the forced numerator. This
does not provide a small estimate for its normalized integral. -/
theorem RelativeBudget.forced_numerator_integrable
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    {σ A Λ δ k : ℝ} (hP : P.Lawful σ A Λ δ k) (x : X) :
    Integrable (forcedNumerator (T.leaf x)) (prior G n) := by
  have hd := poly_integrable_of_envelope (h.full_density_envelope hc ht hP x)
  have hp := Push.SectorMeasure.Env.smul_L1 (P.envelope hP)
    (poly_integrable_of_envelope (h.pass_log_envelope hc ht x))
  have he : forcedNumerator (T.leaf x) =
      (fun U => (T.leaf x).density U - P.eval U • Poly.pass ((T.leaf x).log U)) := by
    funext U
    simpa only [Complex.coe_smul] using forcedNumerator_eq_difference (T.leaf x) U
  rw [he]
  exact hd.sub hp

end YM.Integration.LocalComparison

namespace YM.Integration
open Lattice Wilson RG Marker RG3.Forms RG3.Script.Picnic MeasureTheory Filter
open LocalComparison EngineeringWeightedReadout
open scoped BigOperators Classical

variable {G : Gauge} {C : Family G} {N period level : ℕ}
    {V : Type} [Fintype V] [DecidableEq V] {R : Census V} {X : Type*}
    {o : V → Site (C.side (level + 1) period)}
    {T : Taste X o (C.path.rep N period (level + 1)) R}
    {p : BudgetPoint} {w cost : V → ℝ} {κ regularPrice forcedPrice : ℝ}

/-- Full actual transition of the marked density, divided by its actual
coarse vacuum, with the unmarked unit removed. -/
def actualLocalDensityError
    (T : Taste X o (C.path.rep N period (level + 1)) R)
    (x : X) (W : Config G (C.side level period)) : Poly R :=
  normalized C N period level (actualPush C N period level (T.leaf x).density) W - 1

/-- The entire mixed forced numerator, pushed with the same actual kernel
and divided by the same full outgoing vacuum. -/
def actualForcedDensityError
    (T : Taste X o (C.path.rep N period (level + 1)) R)
    (x : X) (W : Config G (C.side level period)) : Poly R :=
  normalized C N period level
    (actualPush C N period level (forcedNumerator (T.leaf x))) W

theorem actualRegularRemainder_eq_average (hC : C.Makes) (hl : level < N)
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v)
    (ht : p.threshold = (C.path.rep N period (level + 1)).p.threshold)
    (x : X) (W : Config G (C.side level period)) :
    actualRegularRemainder T x W =
      actualAverage C (N := N) (fun U => Poly.pass ((T.leaf x).log U) - 1) W := by
  have he := h.regular_error_envelope hc ht x
  obtain ⟨b, hb⟩ := he.cost
  have hi := actualAverage_integrable C hC hl he.meas.aestronglyMeasurable hb W
  ext s
  let L : Poly R →L[ℝ] ℂ := (Poly.get s).restrictScalars ℝ
  symm
  change L (∫ U, actualConditionalDensity C N period level W U •
    (Poly.pass ((T.leaf x).log U) - 1) ∂prior G _) = _
  rw [← L.integral_comp_comm hi]
  apply integral_congr_ae
  exact ae_of_all _ fun U => L.map_smul _ _

/-- Exact normalized regular/forced split on the original physical history.
All integrability requirements are derived from the native budget and
actual representation. No inverse-gas or forced-smallness premise is used. -/
theorem actualLocalDensityError_split (hC : C.Makes) (hl : level < N)
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v)
    (ht : p.threshold = (C.path.rep N period (level + 1)).p.threshold)
    (x : X) (W : Config G (C.side level period)) :
    actualLocalDensityError T x W =
      actualRegularRemainder T x W + actualForcedDensityError T x W := by
  let P := C.path.rep N period (level + 1)
  let K := C.path.levels.clock.op level period
  let β := C.path.β N period (level + 1)
  let reg : Config G (C.side (level + 1) period) → Poly R :=
    fun U => P.eval U • (Poly.pass ((T.leaf x).log U) - 1)
  let force := forcedNumerator (T.leaf x)
  let vacuum : Config G (C.side (level + 1) period) → Poly R := fun U => P.eval U • 1
  have hP := (hC.wilson.represents N period (level + 1) hl).good
  have hk := C.path.levels.transition_mass level period β
  have hreg : Integrable reg (prior G _) :=
    Push.SectorMeasure.Env.smul_L1 (P.envelope hP)
      (LocalComparison.poly_integrable_of_envelope (h.regular_error_envelope hc ht x))
  have hforce : Integrable force (prior G _) := h.forced_numerator_integrable hc ht hP x
  have hvac : Integrable vacuum (prior G _) := (P.envelope hP).integrable (prior G _) |>.smul_const _
  have he : (T.leaf x).density = reg + force + vacuum := by
    funext U
    have hh := (sub_eq_iff_eq_add).mp (density_error_split (T.leaf x) U)
    simpa only [reg, force, vacuum, P, forcedNumerator, Pi.add_apply,
      Complex.coe_smul] using hh
  change ((C.path.rep N period level).eval W)⁻¹ •
    K.push β (T.leaf x).density W - 1 = actualRegularRemainder T x W +
      ((C.path.rep N period level).eval W)⁻¹ • K.push β force W
  rw [he, StepData.push_add hk (reg + force) vacuum (hreg.add hforce) hvac,
    StepData.push_add hk reg force hreg hforce]
  simp only [Pi.add_apply, smul_add]
  have hr := actualAverage_push C (N := N)
    (fun U => Poly.pass ((T.leaf x).log U) - 1) W
  have hv := actualAverage_push C (N := N) (fun _ => (1 : Poly R)) W
  change actualAverage C (N := N) (fun U => Poly.pass ((T.leaf x).log U) - 1) W =
    ((C.path.rep N period level).eval W)⁻¹ • K.push β reg W at hr
  change actualAverage C (N := N) (fun _ => (1 : Poly R)) W =
    ((C.path.rep N period level).eval W)⁻¹ • K.push β vacuum W at hv
  rw [← hr, ← hv, actualAverage_const C hC hl, ← actualRegularRemainder_eq_average hC hl h hc ht]
  abel

/-- The regular contribution to the full actual normalized error has the
same coefficientwise uniform price. Only the displayed forced error remains
to be estimated, with its actual denominator and mixed products intact. -/
theorem actualLocalDensityError_regular_uniform_price (hC : C.Makes) (hl : level < N)
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v)
    (ht : p.threshold = (C.path.rep N period (level + 1)).p.threshold) (x₀ : X) :
    UniformPolynomialComparison.uniformPrice (fun v => w v / cost v)
      (fun z : X × Config G (C.side level period) =>
        actualLocalDensityError T z.1 z.2 - actualForcedDensityError T z.1 z.2) ≤
      Real.exp (Fintype.card V * regularPrice) - 1 := by
  have he : (fun z : X × Config G (C.side level period) =>
      actualLocalDensityError T z.1 z.2 - actualForcedDensityError T z.1 z.2) =
      (fun z => actualRegularRemainder T z.1 z.2) := by
    funext z
    rw [actualLocalDensityError_split hC hl h hc ht, add_sub_cancel_right]
  rw [he]
  exact actual_regular_uniform_price hC hl h hc ht x₀

variable {I Y : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- Genuine native supplier-to-readout estimate for the full normalized
local error. The forced contribution stays inside the same extraction map,
so no cancellation or engineering weight in that map is discarded. -/
theorem actualLocalDensityError_readout (hC : C.Makes) (hl : level < N)
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v)
    (ht : p.threshold = (C.path.rep N period (level + 1)).p.threshold)
    (L : (I → ℂ) →L[ℂ] Y) (x : I → X)
    (W : I → Config G (C.side level period)) (s : I → R.Mode) :
    ‖L (fun i => (actualLocalDensityError T (x i) (W i)).part (s i))‖ ≤
      columnPrice L (fun i => modeCost w cost (s i)) *
        (Real.exp (Fintype.card V * regularPrice) - 1) +
      ‖L (fun i => (actualForcedDensityError T (x i) (W i)).part (s i))‖ := by
  have he : (fun i => (actualLocalDensityError T (x i) (W i)).part (s i)) =
      (fun i => (actualRegularRemainder T (x i) (W i)).part (s i)) +
      (fun i => (actualForcedDensityError T (x i) (W i)).part (s i)) := by
    funext i
    rw [actualLocalDensityError_split hC hl h hc ht, Poly.part_plus, Pi.add_apply]
  rw [he, map_add]
  exact (norm_add_le _ _).trans
    (add_le_add (actual_regular_readout hC hl h hc ht L x W s) le_rfl)

end YM.Integration
