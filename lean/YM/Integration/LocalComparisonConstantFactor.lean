import YM.Integration.LocalComparisonNativeNonquiet
import YM.Integration.NativeCanonicalRelativeReclosure

/-! The unmasked units and captions of a Taste are field-independent.
Keep their complete polynomial as a scalar factor rather than creating
off-Healthy forced terms. The native residual keeps the original masked
rays and every original forced partner on the same Rep. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay
open RG3.Forms RG3.Script.Picnic MergeProof MergeProof.Accent Push
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type} {X : Type*}
    [DecidableEq V] [Fintype V] {R : Census V} {P : Rep G n}
    {o : V → Site n} (T : Taste X o P R)

def constantLog (x : X) : Poly R :=
  (∑ v, Poly.send (R.fire v) (T.menu.global x v)) +
    ∑' i, Poly.send (T.tag i) (T.score x i)

def nativeRayLog (x : X) (U : Config G n) : Poly R :=
  ∑' i, (T.leaf x).contents.ray i U

def nativeRays (x : X) : Support n → Config G n → Poly R :=
  OverlayFiniteRegular.row (T.leaf x).contents

def nativeResidual (x : X) (U : Config G n) : Poly R :=
  (Real.exp (P.exponent U) : ℂ) •
    (Poly.pass (nativeRayLog T x U) * (T.leaf x).contents.cluster U)

theorem log_constant_split (x : X) (U : Config G n) :
    (T.leaf x).log U = constantLog T x + nativeRayLog T x U := by
  change ((∑ v, Poly.send (R.fire v) (T.menu.global x v)) +
      ∑' i, (T.leaf x).contents.ray i U) +
      (∑' i, Poly.send (T.tag i) (T.score x i)) =
    ((∑ v, Poly.send (R.fire v) (T.menu.global x v)) +
      ∑' i, Poly.send (T.tag i) (T.score x i)) +
      ∑' i, (T.leaf x).contents.ray i U
  abel

variable {T} {p : BudgetPoint} {w cost : V → ℝ}
    {κ regularPrice forcedPrice : ℝ}

private theorem ray_summable
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    (x : X) (U : Config G n) :
    Summable (fun i => (T.leaf x).contents.ray i U) := by
  obtain ⟨b, d, _, _, hF, _, _⟩ := h.native_regular hc ht x
  exact (hF.repair (relativeRadii_positive h.budget.radii hc) (x, U)).2

private theorem caption_summable
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold) (x : X) :
    Summable (fun i => Poly.send (T.tag i) (T.score x i)) := by
  obtain ⟨b, d, _, _, _, hC, _⟩ := h.native_regular hc ht x
  exact (hC.repair (relativeRadii_positive h.budget.radii hc)
    (x, (1 : Config G n))).2

theorem RelativeBudget.constantLog_quiet
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold) (x : X) :
    (constantLog T x).part R.quiet = 0 := by
  rw [constantLog, Poly.part_plus, Poly.part_sum,
    Poly.share (caption_summable h hc ht x)]
  have hu : (∑ v, (Poly.send (R.fire v) (T.menu.global x v)).part R.quiet) = 0 := by
    apply sum_eq_zero
    intro v _
    rw [Poly.part_send, if_neg (R.fire_hot v).symm]
  have hs : (∑' i, (Poly.send (T.tag i) (T.score x i)).part R.quiet) = 0 := by
    refine (tsum_congr (fun i => ?_)).trans tsum_zero
    rw [Poly.part_send]
    apply if_neg
    intro he
    exact ((h.budget.active x).captions.card i).ne_empty (congrArg Subtype.val he.symm)
  rw [hu, hs, add_zero]

theorem RelativeBudget.nativeRayLog_quiet
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    (x : X) (U : Config G n) :
    (nativeRayLog T x U).part R.quiet = 0 := by
  rw [nativeRayLog, Poly.share (ray_summable h hc ht x U)]
  exact (tsum_congr (fun i => (h.native_ray_burns hc x i).sil U)).trans tsum_zero

/-- Exact field-independent factorization, with the full original gas. -/
theorem RelativeBudget.density_constant_factor
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    (x : X) (U : Config G n) :
    (T.leaf x).density U = Poly.pass (constantLog T x) * nativeResidual T x U := by
  unfold Deck.density
  rw [log_constant_split, Extra.Trajectories.pass_add
    (h.constantLog_quiet hc ht x) (h.nativeRayLog_quiet hc ht x U)]
  unfold nativeResidual
  rw [mul_assoc, mul_smul_comm]

/-- The constant correction remains a separate signed polynomial. No
quiet background is charged to the native marked-forced error. -/
theorem RelativeBudget.density_constant_error
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    (x : X) (U : Config G n) :
    (T.leaf x).density U - (P.eval U : ℂ) • (1 : Poly R) =
      Poly.pass (constantLog T x) *
        (nativeResidual T x U - (P.eval U : ℂ) • (1 : Poly R)) +
      (Poly.pass (constantLog T x) - 1) * ((P.eval U : ℂ) • (1 : Poly R)) := by
  rw [h.density_constant_factor hc ht]
  ring

private theorem nativeRays_part
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    (x : X) (s : Support n) (U : Config G n) (q : R.Mode) :
    (nativeRays T x s U).part q =
      ∑' i : {i : ℕ // T.menu.branch i = s}, ((T.leaf x).contents.ray i.val U).part q :=
  Poly.share ((ray_summable h hc ht x U).comp_injective Subtype.val_injective) q

theorem RelativeBudget.nativeRays_burns
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    (x : X) (s : Support n) : Burns o s (nativeRays T x s) P.p.threshold := by
  have hb (i : {i : ℕ // T.menu.branch i = s}) :
      Burns o s ((T.leaf x).contents.ray i.val) P.p.threshold := by
    simpa only [i.property] using h.native_ray_burns hc x i.val
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro U W hUW hFlags
    exact tsum_congr (fun i => (hb i).home U W hUW hFlags)
  · intro g U
    exact tsum_congr (fun i => (hb i).turns g U)
  · intro q
    have he : (fun U => (nativeRays T x s U).part q) =
        (fun U => ∑' i : {i : ℕ // T.menu.branch i = s},
          ((T.leaf x).contents.ray i.val U).part q) :=
      funext (fun U => nativeRays_part h hc ht x s U q)
    rw [he]
    exact Measurable.tsum (fun i => (hb i).me q)
  · intro U q hq
    rw [nativeRays_part h hc ht]
    exact (tsum_congr (fun i => (hb i).scope U q hq)).trans tsum_zero
  · intro U hu
    by_contra hn
    apply hu
    exact (tsum_congr (fun i => not_ne_iff.mp (mt ((hb i).permits U) hn))).trans tsum_zero
  · intro U
    rw [nativeRays_part h hc ht]
    exact (tsum_congr (fun i => (hb i).sil U)).trans tsum_zero

theorem RelativeBudget.nativeRays_sum
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    (x : X) (U : Config G n) :
    (∑ s, nativeRays T x s U) = nativeRayLog T x U := by
  change (∑ s : Support n, cram T.menu.branch
    (fun i => (T.leaf x).contents.ray i U) s) = _
  rw [← tsum_fintype (L := .unconditional (Support n))]
  exact ((ray_summable h hc ht x U).hasSum.tsum_fiberwise T.menu.branch).tsum_eq

/-- Finite original-support rows retain the regular price before all tests. -/
theorem RelativeBudget.nativeRays_towed
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold) (x₀ : X) :
    Towed (relativeRadii w cost) id
      (fun s (z : X × Config G n) => nativeRays T z.1 s z.2)
      p.B p.supportExponent (Fintype.card V * regularPrice) := by
  obtain ⟨b, d, hb, hd, hF, _, htotal⟩ := h.native_regular hc ht x₀
  have h0 : 0 ≤ ∑ v, relativeRadii w cost v * ‖T.menu.global x₀ v‖ :=
    sum_nonneg (fun v _ => mul_nonneg (relativeRadii_positive h.budget.radii hc v).le (norm_nonneg _))
  have hB : b ≤ Fintype.card V * regularPrice := by linarith [htotal x₀]
  exact (towing T.menu.branch
    (fun i (z : X × Config G n) => (T.leaf z.1).contents.ray i z.2)
    hF (relativeRadii_positive h.budget.radii hc)).shrink le_rfl hB
      (relativeRadii_positive h.budget.radii hc)

omit [Fintype V] in
private theorem towed_at {I : Type*} {s : I → Support n}
    {F : I → X × Config G n → Poly R} {r : V → ℝ}
    {m : ℕ} {e c : ℝ} (h : Towed r s F m e c) (x : X) :
    Towed r s (fun i U => F i (x, U)) m e c := by
  obtain ⟨a, ha, hHit, hLoci⟩ := h
  refine ⟨a, ha, hHit, ?_⟩
  intro i
  obtain ⟨b, hb, hbound, hprice⟩ := hLoci i
  exact ⟨b, hb, fun U => hbound (x, U), hprice⟩

theorem RelativeBudget.nativeResidual_play
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    {quietPrice : ℝ} (hK : P.activities.KBound p quietPrice) (x : X) :
    nativeResidual T x = play P R
      (fun box U => OverlayForcedBarcode.full (T.leaf x).contents box U)
      (fun U => ∑ s, nativeRays T x s U) := by
  funext U
  unfold nativeResidual play
  dsimp only
  rw [h.nativeRays_sum hc ht x U, h.native_cluster hc hK x U]

/-- The native residual is Served at the original regular and marked-K
prices. Field-constant captions do not enter the forced error bill. -/
theorem RelativeBudget.nativeResidual_served
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    (hblock : p.B = P.p.B) {δ ε quietPrice : ℝ}
    (hV : P.activities.Valid P.p δ ε) (hK : P.activities.KBound p quietPrice) (x : X) :
    Served P (NativeCanonicalReclosure.regularSingleton (nativeRays T x))
      (NativeCanonicalReclosure.forcedSingleton
        (fun box U => OverlayForcedBarcode.full (T.leaf x).contents box U))
      (nativeResidual T x) o (relativeRadii w cost) p.supportExponent
      (max (Fintype.card V * regularPrice) (Fintype.card V * (κ * forcedPrice))) := by
  have hR := towed_at (h.nativeRays_towed hc ht x) x
  have hG := towed_at (h.native_nonquiet hc hK x) x
  rw [hblock] at hR hG
  rw [h.nativeResidual_play hc ht hK x]
  exact NativeCanonicalReclosure.served_nonquiet_separate P o (relativeRadii w cost)
    (relativeRadii_positive h.budget.radii hc) (nativeRays T x)
    (fun box U => OverlayForcedBarcode.full (T.leaf x).contents box U)
    (fun s => h.nativeRays_burns hc ht x s)
    (fun box => h.native_full_flow hc hblock hV x box)
    (fun box U => h.native_full_quiet hc hblock hV x box U) hR hG

end YM.Integration.LocalComparison
