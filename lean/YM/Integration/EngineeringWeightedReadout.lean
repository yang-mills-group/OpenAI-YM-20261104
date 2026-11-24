import YM.Integration.LocalComparisonForcedDecomposition
import YM.Integration.ReaderFiniteExtraction
import YM.PhysMS.Frame.Measured

/-! Finite probe extraction with the original engineering envelopes retained.

The nonlinear regular/caption bound below is obtained from the native
`RelativeBudget`, not from an assumed scalar comparison error. The full-density
version keeps its forced-cluster numerator explicit. The fixed-detector map
uses the original Reader, output inverse and family; lower-grade cancellations
are identities before any norm estimate. No claim is made that its column
price is uniformly bounded, or that a concrete MS candidate is already known. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.EngineeringWeightedReadout
open Lattice Wilson RG Marker Finset RG3.Forms RG3.Script.Picnic
open LocalComparison UniformPolynomialComparison
open scoped BigOperators Classical

section Columns
variable {I Y : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- Every input envelope is charged against its own actual extraction column. -/
def columnPrice (L : (I → ℂ) →L[ℂ] Y) (a : I → ℝ) : ℝ :=
  ∑ i, a i * ‖L (Pi.single i 1)‖

theorem column_bound (L : (I → ℂ) →L[ℂ] Y) (z : I → ℂ)
    (a : I → ℝ) (ha : ∀ i, ‖z i‖ ≤ a i) :
    ‖L z‖ ≤ columnPrice L a := by
  have hz : z = ∑ i, z i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Pi.single_apply]
  rw [hz, map_sum]
  apply (norm_sum_le _ _).trans
  unfold columnPrice
  apply sum_le_sum
  intro i _
  rw [map_smul, norm_smul]
  exact mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _)

theorem column_bound_scaled (L : (I → ℂ) →L[ℂ] Y) (z : I → ℂ)
    (a : I → ℝ) (b : ℝ) (ha : ∀ i, ‖z i‖ ≤ a i * b) :
    ‖L z‖ ≤ columnPrice L a * b := by
  apply (column_bound L z (fun i => a i * b) ha).trans_eq
  unfold columnPrice
  rw [sum_mul]
  exact sum_congr rfl fun i _ => by ring
end Columns

section Native
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
    {G : Gauge} {n : Side} {X : Type*} {P : Rep G n} {o : V → Site n}
    {T : Taste X o P R} {p : BudgetPoint} {w cost : V → ℝ}
    {κ regularPrice forcedPrice : ℝ}

/-- The exact coefficient envelope, including every declared input cost. -/
def modeCost (w cost : V → ℝ) (s : R.Mode) : ℝ :=
  envelopeProduct cost s / Poly.toll w s

omit [Fintype V] in
private theorem coefficient_of_price (hw : ∀ v, 0 < w v)
    (hc : ∀ v, 0 < cost v) (A : Poly R) (s : R.Mode) {b : ℝ}
    (hb : Poly.price (fun v => w v / cost v) A ≤ b) :
    ‖A.part s‖ ≤ modeCost w cost s * b := by
  have ht : 0 < Poly.toll (fun v => w v / cost v) s :=
    Poly.worth (fun v => div_pos (hw v) (hc v)) s
  have h : ‖A.part s‖ ≤ b / Poly.toll (fun v => w v / cost v) s :=
    (le_div_iff₀ ht).mpr (by
      simpa only [mul_comm] using
        (Poly.member (fun v => div_pos (hw v) (hc v)) s A).trans hb)
  apply h.trans_eq
  have he : Poly.toll (fun v => w v / cost v) s =
      Poly.toll w s / envelopeProduct cost s := by
    simp only [Poly.toll, envelopeProduct, prod_div_distrib]
  rw [he]
  unfold modeCost
  field_simp [(Poly.worth hw s).ne', (envelopeProduct_positive hc s).ne']

omit [Fintype V] in
private theorem dominated_price {A : Poly R} {Z : Type*} {f : Z → Poly R}
    (hw : ∀ v, 0 < w v) (hp : Positive A) (hd : Dominates A f) (z : Z) :
    Poly.price w (f z) ≤ Poly.price w A := by
  unfold Poly.price
  apply sum_le_sum
  intro s _
  rw [hp.norm]
  exact mul_le_mul_of_nonneg_left (hd z s) (Poly.worth hw s).le

/-- A nonlinear physical coefficient estimate supplied by the complete native
regular/caption receipt; the input engineering envelopes remain explicit. -/
theorem regular_coefficient
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    (x : X) (U : Config G n) (s : R.Mode) :
    ‖(Poly.pass ((T.leaf x).log U) - 1).part s‖ ≤
      modeCost w cost s * (Real.exp (Fintype.card V * regularPrice) - 1) := by
  obtain ⟨A, hp, hd, hb⟩ := h.physical_log_majorant hc x ht
  apply coefficient_of_price h.budget.radii hc
  rw [pass_eq_one_add_tail, add_sub_cancel_left]
  exact (dominated_price (fun v => div_pos (h.budget.radii v) (hc v))
    hp.tail (hd.tail hp) (x, U)).trans
      ((tail_price_le hp (fun v => div_pos (h.budget.radii v) (hc v))).trans
        (sub_le_sub_right (Real.exp_monotone hb) 1))

/-- Measurability comes from the original active marked presentation, restored
from its coefficient-price coordinates. It is not an extra readout hypothesis. -/
theorem regular_log_measurable
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (x : X) : Measurable (fun U => (T.leaf x).log U) := by
  let N := priceNormalized (envelopeProduct cost) T
  have hN : Measurable (fun U => (N.leaf x).log U) :=
    ((N.leaf x).contents.extra_meas (h.budget.active x).articles).add measurable_const
  simpa only [Function.comp_def, N, restoreEnvelope_log] using
    (restoreEnvelope (envelopeProduct cost) h.positive).continuous.measurable.comp hN

theorem regular_coefficient_measurable
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (x : X) (s : R.Mode) :
    Measurable (fun U => (Poly.pass ((T.leaf x).log U) - 1).part s) :=
  (Poly.get s).continuous.measurable.comp
    ((Poly.pass_cont.measurable.comp (regular_log_measurable h x)).sub measurable_const)

variable {I Y : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- Finite probes may choose their test tuples independently. The extraction
map is applied to the actual nonlinear coefficients, before bounding it. -/
theorem regular_readout
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    (L : (I → ℂ) →L[ℂ] Y) (x : I → X) (U : I → Config G n) (s : I → R.Mode) :
    ‖L (fun i => (Poly.pass ((T.leaf (x i)).log (U i)) - 1).part (s i))‖ ≤
      columnPrice L (fun i => modeCost w cost (s i)) *
        (Real.exp (Fintype.card V * regularPrice) - 1) :=
  column_bound_scaled L _ _ _ (fun i => regular_coefficient h hc ht (x i) (U i) (s i))

/-- The full-density version retains the actual vacuum and the entire forced
numerator. No smallness or inverse-vacuum estimate is inserted for that term. -/
theorem full_numerator_readout
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    (L : (I → ℂ) →L[ℂ] Y) (x : I → X) (U : I → Config G n) (s : I → R.Mode) :
    ‖L (fun i => ((T.leaf (x i)).density (U i) -
      (P.eval (U i) : ℂ) • (1 : Poly R)).part (s i))‖ ≤
      columnPrice L (fun i => modeCost w cost (s i) *
        (|P.eval (U i)| * (Real.exp (Fintype.card V * regularPrice) - 1) +
          (Real.exp (P.exponent (U i)) * Real.exp (Fintype.card V * regularPrice)) *
            Poly.price (fun v => w v / cost v)
              (forcedClusterError (T.leaf (x i)) (U i)))) := by
  apply column_bound
  intro i
  exact coefficient_of_price h.budget.radii hc _ _ (h.density_error_price hc ht (x i) (U i))
end Native

section Actual
open MeasureTheory
variable {G : Gauge} {C : Family G} {N period level : ℕ}
    {V : Type} [Fintype V] [DecidableEq V] {R : Census V} {X : Type*}
    {o : V → Site (C.side (level + 1) period)}
    {T : Taste X o (C.path.rep N period (level + 1)) R}
    {p : BudgetPoint} {w cost : V → ℝ} {κ regularPrice forcedPrice : ℝ}

/-- The regular error averaged with the actual transition and the full actual
vacuum. This is a polynomial of the same original marked coefficients. -/
def actualRegularRemainder (T : Taste X o (C.path.rep N period (level + 1)) R)
    (x : X) (W : Config G (C.side level period)) : Poly R :=
  Poly.inject fun s => actualAverage C (N := N)
    (fun U => (Poly.pass ((T.leaf x).log U) - 1).part s) W

theorem actual_regular_integrable (hC : C.Makes) (hl : level < N)
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v)
    (ht : p.threshold = (C.path.rep N period (level + 1)).p.threshold)
    (x : X) (s : R.Mode) (W : Config G (C.side level period)) :
    Integrable (fun U => actualConditionalDensity C N period level W U •
      (Poly.pass ((T.leaf x).log U) - 1).part s) (prior G _) :=
  actualAverage_integrable C hC hl (regular_coefficient_measurable h x s).aestronglyMeasurable
    (fun U => regular_coefficient h hc ht x U s) W

/-- The full actual normalization introduces no extra partition, volume or
test-space factor into the physical regular coefficient estimate. -/
theorem actual_regular_coefficient (hC : C.Makes) (hl : level < N)
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v)
    (ht : p.threshold = (C.path.rep N period (level + 1)).p.threshold)
    (x : X) (s : R.Mode) (W : Config G (C.side level period)) :
    ‖(actualRegularRemainder T x W).part s‖ ≤
      modeCost w cost s * (Real.exp (Fintype.card V * regularPrice) - 1) :=
  actualAverage_norm_le C hC hl (fun U => regular_coefficient h hc ht x U s) W

/-- The supremum over every test tuple and outgoing field remains inside each
coefficient sum after averaging under the original probability law. -/
theorem actual_regular_uniform_price (hC : C.Makes) (hl : level < N)
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v)
    (ht : p.threshold = (C.path.rep N period (level + 1)).p.threshold) (x₀ : X) :
    uniformPrice (fun v => w v / cost v)
      (fun z : X × Config G (C.side level period) => actualRegularRemainder T z.1 z.2) ≤
      Real.exp (Fintype.card V * regularPrice) - 1 := by
  obtain ⟨A, hp, hd, hb⟩ := h.physical_log_majorant hc x₀ ht
  have hdom : Dominates (tail A)
      (fun z : X × Config G (C.side level period) => actualRegularRemainder T z.1 z.2) := by
    intro z s
    apply actualAverage_norm_le C hC hl
    intro U
    simpa only [pass_eq_one_add_tail, add_sub_cancel_left] using (hd.tail hp) (z.1, U) s
  exact (uniformPrice_le hp.tail hdom
    (fun v => div_pos (h.budget.radii v) (hc v))).trans
      ((tail_price_le hp (fun v => div_pos (h.budget.radii v) (hc v))).trans
        (sub_le_sub_right (Real.exp_monotone hb) 1))

variable {I Y : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- Each finite probe can use its own independent tests and conditioning field.
The actual normalization is completed before the fixed linear extraction. -/
theorem actual_regular_readout (hC : C.Makes) (hl : level < N)
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v)
    (ht : p.threshold = (C.path.rep N period (level + 1)).p.threshold)
    (L : (I → ℂ) →L[ℂ] Y) (x : I → X)
    (W : I → Config G (C.side level period)) (s : I → R.Mode) :
    ‖L (fun i => (actualRegularRemainder T (x i) (W i)).part (s i))‖ ≤
      columnPrice L (fun i => modeCost w cost (s i)) *
        (Real.exp (Fintype.card V * regularPrice) - 1) :=
  column_bound_scaled L _ _ _
    (fun i => actual_regular_coefficient hC hl h hc ht (x i) (s i) (W i))
end Actual

section Reader
open OPE OPE.Orbits Spec
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    {F : Final C f S}
    (A : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {D : ℕ} (E : Detector S D) (J : ℝ → PhysMS.tower S)

/-- Original finite detector, original homogeneous Reader cut, and the same
actual output frame inverse, in that order. -/
def fixedReadout (m : ℕ) (r : ℝ) :
    (Fin E.size → ℂ) →L[ℂ] (Climb.Bel C.book).Field m :=
  (LinearMap.toContinuousLinearMap (J r m).symm.toLinearMap).comp
    ((LinearMap.toContinuousLinearMap (A.cutTest m D)).comp
      (LinearMap.toContinuousLinearMap E.report))

theorem fixedReadout_field (m : ℕ) (r : ℝ) (z : S.Field D) :
    fixedReadout A E J m r (fun i => witnessAt S D (E.listen i) z) =
      (J r m).symm (A.cutTest m D z) := by
  change (J r m).symm (A.cutTest m D (E.report _)) = _
  rw [E.recovered]

/-- The preserved packet recovers the original fresh field at every sufficient
output horizon, before the output inverse is applied. -/
theorem fixedReadout_packet {I : Type} [Fintype I] {d : I → ℕ}
    (m : ℕ) (hm : m ≤ D) (r : ℝ) (x : I → E4) (v : Labels S d) (o : E4) :
    fixedReadout A E J m r
      (fun i => witnessAt S D (E.listen i) (A.packet D x v o)) =
      (J r m).symm (A.fresh m x o v) := by
  rw [fixedReadout_field, A.filtered_packet m D hm]

/-- Lower engineering grades cancel in the original readout exactly. This is
an identity for the combined probe array, not a bound on its individual entries. -/
theorem fixedReadout_lower (m q : ℕ) (hq : q ≤ D) (hqm : q < m)
    (r : ℝ) (z : S.Field q) :
    fixedReadout A E J m r (fun i => witnessAt S D (E.listen i)
      (F.sector.derivatives.rise hq z)) = 0 := by
  rw [fixedReadout_field, A.cut_rise m q D hq, A.kills_lower m q hqm, map_zero]

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V} {X : Type*}
    {N period level : ℕ} {p : BudgetPoint}
    {o : V → Site (C.side level period)}
    {T : Taste X o (C.path.rep N period level) R}
    {w cost : V → ℝ} {κ regularPrice forcedPrice : ℝ}

/-- Concrete native supplier-to-Reader application on the same physical family.
Its displayed column price retains the original engineering envelopes and
output inverse; no boundedness of that price is presumed. -/
theorem fixed_regular_readout
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v)
    (ht : p.threshold = (C.path.rep N period level).p.threshold)
    (m : ℕ) (r : ℝ) (x : Fin E.size → X)
    (U : Fin E.size → Config G (C.side level period)) (s : Fin E.size → R.Mode) :
    ‖fixedReadout A E J m r
      (fun i => (Poly.pass ((T.leaf (x i)).log (U i)) - 1).part (s i))‖ ≤
      columnPrice (fixedReadout A E J m r) (fun i => modeCost w cost (s i)) *
        (Real.exp (Fintype.card V * regularPrice) - 1) :=
  regular_readout h hc ht (fixedReadout A E J m r) x U s
end Reader
end YM.Integration.EngineeringWeightedReadout
