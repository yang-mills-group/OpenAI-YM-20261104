import YM.Integration.LocalComparisonNativeRows
import YM.Integration.LocalComparisonEnvelopeDensity

/-!
Restore the announced input envelopes in the native row currency. The rows
are the original physical rows; their radii are divided by the original
per-slot kernel costs. This cancels the coefficient restoration exactly,
including every forced partner and the original quiet K profile.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay
open RG3.Forms RG3.Script.Picnic MergeProof MergeProof.Accent Push Push.AbsoluteSums
open scoped BigOperators Classical

variable {V : Type} [DecidableEq V] {R : Census V}

def relativeRadii (w cost : V → ℝ) : V → ℝ := fun v => w v / cost v

omit [DecidableEq V] in
lemma relativeRadii_positive {w cost : V → ℝ}
    (hw : ∀ v, 0 < w v) (hc : ∀ v, 0 < cost v) (v : V) :
    0 < relativeRadii w cost v := div_pos (hw v) (hc v)

lemma relativeRadii_toll (w cost : V → ℝ) (hc : ∀ v, 0 < cost v) (q : R.Mode) :
    Poly.toll (relativeRadii w cost) q * envelopeProduct cost q = Poly.toll w q := by
  unfold Poly.toll relativeRadii envelopeProduct
  rw [← prod_mul_distrib]
  exact prod_congr rfl (fun v _ => div_mul_cancel₀ (w v) (hc v).ne')

/-- The common coefficient majorant is restored before any test or field is
chosen. Its native payment is exactly unchanged at the relative radii. -/
theorem towed_restoreEnvelope {I Y : Type*} {n : Side} {s : I → Support n}
    {F : I → Y → Poly R} {w : V → ℝ} {M : ℕ} {e c : ℝ}
    (cost : V → ℝ) (hc : ∀ v, 0 < cost v) (h : Towed w s F M e c) :
    Towed (relativeRadii w cost) s
      (fun i y => restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc) (F i y))
      M e c := by
  obtain ⟨a, ha, hHit, hLoci⟩ := h
  refine ⟨a, ha, hHit, ?_⟩
  intro i
  obtain ⟨b, hb, hB, hprice⟩ := hLoci i
  refine ⟨fun q => envelopeProduct cost q * b q,
    fun q => mul_nonneg (envelopeProduct_positive hc q).le (hb q), ?_, ?_⟩
  · intro y q
    change ‖(envelopeProduct cost q : ℂ) * (F i y).part q‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (envelopeProduct_positive hc q)]
    exact mul_le_mul_of_nonneg_left (hB y q) (envelopeProduct_positive hc q).le
  · change (∑ q, Poly.toll (relativeRadii w cost) q * (envelopeProduct cost q * b q)) ≤ a i
    calc
      _ = ∑ q, Poly.toll w q * b q := by
        apply sum_congr rfl
        intro q _
        rw [← mul_assoc, relativeRadii_toll w cost hc q]
      _ ≤ a i := hprice

variable {G : Gauge} {n : Side}

/-- Restoration changes neither physical support nor eligibility. -/
theorem borne_restoreEnvelope {o : V → Site n} {s : Support n}
    {F : Config G n → Poly R} {t : ℝ}
    (cost : R.Mode → ℝ) (hc : ∀ q, 0 < cost q) (h : Borne o s F t) :
    Borne o s (fun U => restoreEnvelope cost hc (F U)) t := by
  refine ⟨fun U W hUW hFlags => congrArg (restoreEnvelope cost hc) (h.home U W hUW hFlags),
    fun k U => congrArg (restoreEnvelope cost hc) (h.turns k U), ?_, ?_⟩
  · intro q
    change Measurable (fun U => (cost q : ℂ) * (F U).part q)
    exact measurable_const.mul (h.me q)
  · intro U q hn
    change (cost q : ℂ) * (F U).part q = 0
    rw [h.scope U q hn, mul_zero]

theorem burns_restoreEnvelope {o : V → Site n} {s : Support n}
    {F : Config G n → Poly R} {t : ℝ}
    (cost : R.Mode → ℝ) (hc : ∀ q, 0 < cost q) (h : Burns o s F t) :
    Burns o s (fun U => restoreEnvelope cost hc (F U)) t := by
  refine ⟨borne_restoreEnvelope cost hc h.toBorne, ?_, ?_⟩
  · intro U hn
    apply h.permits U
    intro hz
    exact hn (by rw [hz, map_zero])
  · intro U
    change (cost R.quiet : ℂ) * (F U).part R.quiet = 0
    rw [h.sil U, mul_zero]

theorem flow_restoreEnvelope {o : V → Site n} {box : Box n}
    {F : Config G n → Poly R} {t : ℝ}
    (cost : R.Mode → ℝ) (hc : ∀ q, 0 < cost q) (h : Flow o box F t) :
    Flow o box (fun U => restoreEnvelope cost hc (F U)) t := by
  refine ⟨borne_restoreEnvelope cost hc h.toBorne, ?_⟩
  intro U hn
  apply h.permits U
  intro hz
  exact hn (by rw [hz, map_zero])

variable {X : Type*} {P : Rep G n} {o : V → Site n}
    {T : Taste X o P R} {p : BudgetPoint} {w cost : V → ℝ}
    {κ regularPrice forcedPrice : ℝ}

private theorem restore_ray (hc : ∀ v, 0 < cost v) (x : X) (i : ℕ) (U : Config G n) :
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)
      (((priceNormalized (envelopeProduct cost) T).leaf x).contents.ray i U) =
      (T.leaf x).contents.ray i U := by
  change restoreEnvelope _ _ (Poly.send (T.menu.rays i)
    (masked P.p.threshold (T.menu.branch i)
      (fun W => (envelopeProduct cost (T.menu.rays i))⁻¹ • T.menu.regular x i W) U)) =
    Poly.send (T.menu.rays i) (masked P.p.threshold (T.menu.branch i) (T.menu.regular x i) U)
  by_cases hU : Healthy P.p.threshold (T.menu.branch i) U
  · rw [masked_eq _ _ _ _ hU, masked_eq _ _ _ _ hU]
    exact restoreEnvelope_send _ _ _ _
  · rw [masked_ne _ _ _ _ hU, masked_ne _ _ _ _ hU, Poly.send_zero, map_zero]

/-- Exact original-address restoration commutes with the full barcode sum. -/
theorem restore_full_forced (hc : ∀ v, 0 < cost v) (x : X) (box : Box n) (U : Config G n) :
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)
      (OverlayForcedBarcode.full ((priceNormalized (envelopeProduct cost) T).leaf x).contents box U) =
      OverlayForcedBarcode.full (T.leaf x).contents box U := by
  unfold OverlayForcedBarcode.full tally
  rw [ContinuousLinearEquiv.map_tsum]
  exact tsum_congr (fun i => restoreEnvelope_each T cost hc x i.val U)

variable [Fintype V]

/-- Relative normalization produces native payments for the literal original
regular rays and mixed captions. The original unit channel remains visible. -/
theorem RelativeBudget.native_regular
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (hthreshold : p.threshold = P.p.threshold) (x₀ : X) :
    ∃ b d : ℝ, 0 ≤ b ∧ 0 ≤ d ∧
      Towed (relativeRadii w cost) T.menu.branch
        (fun i (z : X × Config G n) => (T.leaf z.1).contents.ray i z.2)
        p.B p.supportExponent b ∧
      Towed (relativeRadii w cost) T.site
        (fun i (z : X × Config G n) => Poly.send (T.tag i) (T.score z.1 i))
        p.B p.supportExponent d ∧
      ∀ x : X, (∑ v, relativeRadii w cost v * ‖T.menu.global x v‖) + b + d ≤
        Fintype.card V * regularPrice := by
  obtain ⟨b, d, hb, hd, hR, hC, htotal⟩ := h.budget.native_regular hthreshold x₀
  refine ⟨b, d, hb, hd, ?_, ?_, ?_⟩
  · have ht := towed_restoreEnvelope cost hc hR
    have he : (fun i (z : X × Config G n) =>
        restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)
          (((priceNormalized (envelopeProduct cost) T).leaf z.1).contents.ray i z.2)) =
        (fun i (z : X × Config G n) => (T.leaf z.1).contents.ray i z.2) := by
      funext i z
      exact restore_ray hc z.1 i z.2
    rwa [he] at ht
  · have ht := towed_restoreEnvelope cost hc hC
    have he : (fun i (z : X × Config G n) =>
        restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)
          (Poly.send (T.tag i) ((envelopeProduct cost (T.tag i))⁻¹ • T.score z.1 i))) =
        (fun i (z : X × Config G n) => Poly.send (T.tag i) (T.score z.1 i)) := by
      funext i z
      exact restoreEnvelope_send _ _ _ _
    change Towed _ _ (fun i (z : X × Config G n) =>
      restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)
        (Poly.send (T.tag i) ((envelopeProduct cost (T.tag i))⁻¹ • T.score z.1 i))) _ _ _ at ht
    rwa [he] at ht
  · intro x
    have hunit : (∑ v, relativeRadii w cost v * ‖T.menu.global x v‖) ≤
        ∑ v, w v * h.budget.unitBound v := by
      apply sum_le_sum
      intro v _
      have hu := h.budget.unit x v
      change ‖(envelopeProduct cost (R.fire v))⁻¹ • T.menu.global x v‖ ≤ h.budget.unitBound v at hu
      simp only [envelopeProduct, Census.fire, prod_singleton] at hu
      calc
        relativeRadii w cost v * ‖T.menu.global x v‖ =
            w v * ‖(cost v)⁻¹ • T.menu.global x v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hc v))]
          simp only [relativeRadii, div_eq_mul_inv, mul_assoc]
        _ ≤ w v * h.budget.unitBound v := mul_le_mul_of_nonneg_left hu (h.budget.radii v).le
    linarith only [hunit, htotal]

/-- The complete physical forced rows are paid at the same exponent, with
no additional envelope-restoration loss. Original quiet K is included. -/
theorem RelativeBudget.native_full_forced
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) {quietPrice : ℝ}
    (hK : P.activities.KBound p quietPrice) (x₀ : X) :
    Towed (relativeRadii w cost) Prod.fst
      (fun box (z : X × Config G n) => OverlayForcedBarcode.full (T.leaf z.1).contents box z.2)
      p.B p.supportExponent (quietPrice + Fintype.card V * (κ * forcedPrice)) := by
  have ht := towed_restoreEnvelope cost hc (h.budget.native_full_forced hK x₀)
  have he : (fun box (z : X × Config G n) =>
      restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)
        (OverlayForcedBarcode.full ((priceNormalized (envelopeProduct cost) T).leaf z.1).contents box z.2)) =
      (fun box (z : X × Config G n) => OverlayForcedBarcode.full (T.leaf z.1).contents box z.2) := by
    funext box z
    exact restore_full_forced hc z.1 box z.2
  rwa [he] at ht

/-- Healthy support of the original ray follows by the exact invertible
coefficient restoration, without choosing a new representation. -/
theorem RelativeBudget.native_ray_burns
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (x : X) (i : ℕ) :
    Burns o (T.menu.branch i) ((T.leaf x).contents.ray i) P.p.threshold := by
  have ht := burns_restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)
    (OverlayFiniteRegular.ray_burns ((priceNormalized (envelopeProduct cost) T).leaf x).contents
      (h.budget.active x).articles i)
  change Burns T.menu.origins (T.menu.branch i)
    (fun U => restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)
      (((priceNormalized (envelopeProduct cost) T).leaf x).contents.ray i U)) P.p.threshold at ht
  rw [T.root] at ht
  have he : (fun U => restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)
      (((priceNormalized (envelopeProduct cost) T).leaf x).contents.ray i U)) =
      (T.leaf x).contents.ray i := funext (restore_ray hc x i)
  rwa [he] at ht

/-- Every mixed caption keeps its complete declared support and is left
unmasked for the native caption-remasking step. -/
theorem RelativeBudget.native_caption_borne
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (x : X) (i : ℕ) :
    Borne o (T.site i) (fun _ : Config G n => Poly.send (T.tag i) (T.score x i)) P.p.threshold := by
  refine ⟨fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ => measurable_const, ?_⟩
  intro U
  apply GridApprox.Nil.scope_send
  intro v hv
  have ht : T.menu.origins v ∈ T.site i := (h.budget.active x).captions.pins i v hv
  change o v ∈ T.site i
  simpa only [T.root] using ht

/-- Original countable forced rows are restored before barcode aggregation. -/
theorem RelativeBudget.native_each
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) {quietPrice : ℝ}
    (hK : P.activities.KBound p quietPrice) (x₀ : X) :
    Towed (relativeRadii w cost) (fun i => (P.activities.forced i).support)
      (fun i (z : X × Config G n) => (T.leaf z.1).contents.each i z.2)
      p.B p.supportExponent (quietPrice + Fintype.card V * (κ * forcedPrice)) := by
  have ht := towed_restoreEnvelope cost hc (h.budget.native_each hK x₀)
  have he : (fun i (z : X × Config G n) =>
      restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)
        (((priceNormalized (envelopeProduct cost) T).leaf z.1).contents.each i z.2)) =
      (fun i (z : X × Config G n) => (T.leaf z.1).contents.each i z.2) := by
    funext i z
    exact restoreEnvelope_each T cost hc z.1 i z.2
  rwa [he] at ht

/-- The finite full-row field is the literal original compulsory-cover gas. -/
theorem RelativeBudget.native_cluster
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) {quietPrice : ℝ}
    (hK : P.activities.KBound p quietPrice) (x : X) (U : Config G n) :
    (T.leaf x).contents.cluster U =
      field (fun box => OverlayForcedBarcode.full (T.leaf x).contents box U)
        (flags P.p.threshold U) := by
  have hw := relativeRadii_positive h.budget.radii hc
  exact (Accent.rock_out P.activities P.p U (fun i => (T.leaf x).contents.each i U) hw
    ((h.native_each hc hK x).repair hw (x, U)).1).symm

private theorem FullBudget.native_glow
    (h : FullBudget p T w κ regularPrice forcedPrice)
    (hblock : p.B = P.p.B) (x : X) :
    GapsI.Seat.Glow (T.leaf x).contents w p.supportExponent
      (Fintype.card V * (κ * forcedPrice)) := by
  obtain ⟨a, ha, hHit, hLoci⟩ := h.native_marked x
  choose b hb hbound hprice using hLoci
  let c (i : ℕ × ℕ) := b i (T.menu.marks i.1 i.2)
  have hc i : 0 ≤ c i := hb i _
  have hcost i : Poly.toll w (T.menu.marks i.1 i.2) * c i ≤ a i := by
    exact (single_le_sum (fun q _ => mul_nonneg (Poly.worth h.radii q).le (hb i q))
      (mem_univ (T.menu.marks i.1 i.2))).trans (hprice i)
  refine ⟨c, ?_, ?_⟩
  · intro i U
    have ht := hbound i (x, U) (T.menu.marks i.1 i.2)
    change ‖(Poly.send (T.menu.marks i.1 i.2) (T.menu.force x i.1 i.2 U)).part
      (T.menu.marks i.1 i.2)‖ ≤ _ at ht
    change ‖T.menu.force x i.1 i.2 U‖ ≤ b i (T.menu.marks i.1 i.2)
    simpa only [Poly.part_send, ite_true] using ht
  · rw [hblock] at hHit
    intro z
    apply budget_mono (hHit z)
    · intro i
      split_ifs
      · exact mul_nonneg (mul_nonneg (Poly.worth h.radii _).le (hc i)) (Real.exp_pos _).le
      · rfl
    · intro i
      split_ifs
      · exact mul_le_mul_of_nonneg_right (hcost i) (Real.exp_pos _).le
      · rfl

/-- The complete restored rows retain actual native force eligibility. -/
theorem RelativeBudget.native_full_flow
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (hblock : p.B = P.p.B) {δ ε : ℝ}
    (hV : P.activities.Valid P.p δ ε) (x : X) (box : Box n) :
    Flow o box (fun U => OverlayForcedBarcode.full (T.leaf x).contents box U) P.p.threshold := by
  have hG := h.budget.native_glow hblock x
  have hF := OverlayForcedBarcode.flow
    ((priceNormalized (envelopeProduct cost) T).leaf x).contents hG h.budget.radii hV
    (h.budget.active x).articles (σ := 0) le_rfl p.exponent_pos.le P.p.exponent_pos.le box
  have ht := flow_restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc) hF
  change Flow T.menu.origins box (fun U =>
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)
      (OverlayForcedBarcode.full ((priceNormalized (envelopeProduct cost) T).leaf x).contents box U))
    P.p.threshold at ht
  rw [T.root] at ht
  have he : (fun U =>
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hc)
      (OverlayForcedBarcode.full ((priceNormalized (envelopeProduct cost) T).leaf x).contents box U)) =
    (fun U => OverlayForcedBarcode.full (T.leaf x).contents box U) :=
    funext (restore_full_forced hc x box)
  rwa [he] at ht

/-- The exact original quiet K profile is preserved by relative restoration. -/
theorem RelativeBudget.native_full_quiet
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (hblock : p.B = P.p.B) {δ ε : ℝ}
    (hV : P.activities.Valid P.p δ ε) (x : X) (box : Box n) (U : Config G n) :
    (OverlayForcedBarcode.full (T.leaf x).contents box U).part R.quiet =
      profile P.activities (fun i => Complex.ofReal ∘ P.activities.K i) box U := by
  have hG := h.budget.native_glow hblock x
  have hq := OverlayForcedBarcode.quiet
    ((priceNormalized (envelopeProduct cost) T).leaf x).contents hG h.budget.radii hV
    (h.budget.active x).articles (σ := 0) le_rfl p.exponent_pos.le P.p.exponent_pos.le box U
  have he := congrArg (fun A : Poly R => A.part R.quiet) (restore_full_forced (T := T) hc x box U)
  change (envelopeProduct cost R.quiet : ℂ) * _ = _ at he
  have hz : envelopeProduct cost R.quiet = 1 := by simp [envelopeProduct, Census.quiet]
  rw [hz, Complex.ofReal_one, one_mul] at he
  exact he.symm.trans hq

end YM.Integration.LocalComparison
