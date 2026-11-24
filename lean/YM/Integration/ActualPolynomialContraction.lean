import YM.Integration.ActualSignedCore

/-! Weighted coefficient prices contract through the literal positive
conditional kernels. The original full vacuum is retained at both ends.
The input price is supplied explicitly; no forced-tail or localization
estimate is inferred from this contraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualPolynomialContraction
open Function Finset MeasureTheory Lattice Wilson RG Marker
open scoped BigOperators Classical

variable {V : Type} [DecidableEq V] {B : Census V}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma price_integrable (w : V → ℝ) {F : Ω → Poly B}
    (hF : Integrable F μ) : Integrable (fun U => Poly.price w (F U)) μ := by
  unfold Poly.price
  exact integrable_finsetSum _ (fun q _ =>
    (((Poly.get q).restrictScalars ℝ).integrable_comp hF).norm.const_mul _)

lemma price_integral_le {w : V → ℝ} (hw : ∀ i, 0 < w i)
    {F : Ω → Poly B} (hF : Integrable F μ) :
    Poly.price w (∫ U, F U ∂μ) ≤ ∫ U, Poly.price w (F U) ∂μ := by
  unfold Poly.price
  have hI (q : B.Mode) : Integrable (fun U => Poly.toll w q * ‖(F U).part q‖) μ :=
    (((Poly.get q).restrictScalars ℝ).integrable_comp hF).norm.const_mul _
  rw [integral_finsetSum Finset.univ (fun q _ => hI q)]
  apply Finset.sum_le_sum
  intro q _
  rw [integral_const_mul]
  let L := (Poly.get q).restrictScalars ℝ
  change Poly.toll w q * ‖L (∫ U, F U ∂μ)‖ ≤
    Poly.toll w q * ∫ U, ‖L (F U)‖ ∂μ
  rw [← L.integral_comp_comm hF]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Poly.worth hw q).le

lemma price_real_smul (w : V → ℝ) (F : Poly B) {a : ℝ} (ha : 0 ≤ a) :
    Poly.price w (a • F) = a * Poly.price w F := by
  rw [← Complex.coe_smul, Poly.adapted, Complex.norm_real, Real.norm_of_nonneg ha]

variable {G : Gauge} (C : Family G) (hC : C.Makes) {N p j m : ℕ}
    {w : V → ℝ} (hw : ∀ i, 0 < w i)
include hC hw

lemma average_price_le (hm : m < N)
    {F : Config G (C.side (m+1) p) → Poly B} {K : ℝ}
    (hF : AEStronglyMeasurable F (prior G _))
    (hK : ∀ U, Poly.price w (F U) ≤ K)
    (U : Config G (C.side m p)) :
    Poly.price w (actualAverage C (N := N) F U) ≤ K := by
  obtain ⟨r, hr, hbound⟩ := Poly.equivalent_norm (R := B) hw
  have hn (W) : ‖F W‖ ≤ K*r :=
    (hbound _).trans (mul_le_mul_of_nonneg_right (hK W) hr)
  have hI := actualAverage_integrable C hC hm hF hn U
  have hD := actualConditionalDensity_integrable C hC hm U
  unfold actualAverage
  apply (price_integral_le hw hI).trans
  calc
    _ ≤ ∫ W, actualConditionalDensity C N p m U W * K ∂prior G _ :=
      integral_mono (price_integrable w hI) (hD.mul_const K) (fun W => by
        rw [price_real_smul w _ (actualConditionalDensity_nonneg C hC hm U W)]
        exact mul_le_mul_of_nonneg_left (hK W)
          (actualConditionalDensity_nonneg C hC hm U W))
    _ = K := by
      rw [integral_mul_const, actualConditionalDensity_total C hC hm U, one_mul]

lemma transport_price_le (hj : j ≤ N)
    {F : Config G (C.side j p) → Poly B} {K : ℝ}
    (hF : AEStronglyMeasurable F (prior G _))
    (hK : ∀ U, Poly.price w (F U) ≤ K) (hm : m ≤ j)
    (U : Config G (C.side m p)) :
    Poly.price w (actualTransport C (N := N) F hm U) ≤ K := by
  obtain ⟨r, hr, hbound⟩ := Poly.equivalent_norm (R := B) hw
  have hn (W) : ‖F W‖ ≤ K*r :=
    (hbound _).trans (mul_le_mul_of_nonneg_right (hK W) hr)
  induction hm using Nat.decreasingInduction with
  | self => rw [actualTransport_base C hC hj]; exact hK U
  | of_succ l hl ih =>
    rw [actualTransport_step C hC hj F hl]
    exact average_price_le C hC hw (hl.trans_le hj)
      (actualTransport_integrable C hC hj hF hn hl).aestronglyMeasurable ih U

/-- The exact numerator price is divided by its own fine vacuum. Neither
an inverse-vacuum bound nor a volume or mode-count factor is introduced. -/
lemma signed_price_le (hj : j ≤ N)
    {X : Config G (C.side j p) → Poly B} {K : ℝ}
    (hX : Integrable X (prior G _))
    (hK : ∀ U, Poly.price w (X U) ≤ (C.path.rep N p j).eval U * K)
    (hm : m ≤ j) (U : Config G (C.side m p)) :
    Poly.price w (actualSignedTransport C (N := N) X hm U) ≤ K := by
  have hD : AEStronglyMeasurable (fun W => ((C.path.rep N p j).eval W)⁻¹)
      (prior G _) := ((C.path.rep N p j).envelope
    (hC.wilson.represents N p j hj).good).meas.inv.aestronglyMeasurable
  apply transport_price_le C hC hw hj (hD.smul hX.aestronglyMeasurable) _ hm U
  intro W
  have hp := Multi.AxisShift.chosen_positive hC.wilson hj W
  change Poly.price w (((C.path.rep N p j).eval W)⁻¹ • X W) ≤ K
  rw [price_real_smul w _ (inv_nonneg.mpr hp.le)]
  exact (mul_le_mul_of_nonneg_left (hK W) (inv_nonneg.mpr hp.le)).trans_eq (by
    rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul])

end YM.Integration.ActualPolynomialContraction
