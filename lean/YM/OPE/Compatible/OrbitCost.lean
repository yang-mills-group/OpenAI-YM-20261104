import YM.OPE.Compatible.Beam
import YM.OPE.Exchange.Regime

/-!
# Transfer costs through the detector projection

Any finite signed residual (indices/seams/coefficients may be dependent)
shrinking about one center, measured by actual hierarchy values against all
fixed exteriors with fixed positive clearance. The hypotheses require rates
*also* with positions varying in the indicated geometry, but **not** growing
exterior labels. These estimates survive all fixed-level orbit readouts.
The proof keeps the entire signed residual, doesn't take the sum of separate
absolute errors on a larger positive hull.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G:Gauge} {L:Register G} {S:Table L} {l J:Type} [Fintype J]
  {φ : Filter l} {T : l → ℝ} {κ : ℝ}
lemma RateLE.linear {X Y:Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {x : l → X} (hx : RateLE φ T x κ)
    (hT : Tendsto T φ atTop) (F : X →L[ℝ] Y) : RateLE φ T (fun i => F (x i)) κ :=
  (((RateLE.const ‖F‖ hT).mul hx.norm).mono (zero_add _|>.le)).of_norm_le (Eventually.of_forall fun i => F.le_opNorm (x i))
namespace Cov

lemma RateLocations (e : Exterior L) (K : l → Ortho) (o : l → E4) : ∃ δ : ℝ, 0 < δ ∧
    ∀ i, ClearOf (o i) (fun j => Survey.placements e (K i) j + o i) δ := by
  let B := bearing e
  have hf i : 0 < ‖B i‖ := norm_pos_iff.mpr (((beside_distinct.mp (bearing_clear e)).2.2 () i).symm)
  have hh i j (h : i ≠ j) : 0 < ‖B i - B j‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr ((beside_distinct.mp (bearing_clear e)).2.1.ne h))
  have he : ∀ᶠ δ : ℝ in 𝓝[>] 0, (∀ i, δ < ‖B i‖) ∧ ∀ i j, i ≠ j → δ < ‖B i-B j‖ := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    exact (eventually_all.mpr (fun i => gt_mem_nhds (hf i))).and
      (eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun h => gt_mem_nhds (hh i j h))
  obtain ⟨d,h,hρ⟩ := (he.and self_mem_nhdsWithin).exists
  refine ⟨d,hρ,fun i => ⟨fun j => ?_,fun j k e' => ?_⟩⟩
  · rw [norm_sub_rev, add_sub_cancel_right]; exact (h.1 j).le.trans_eq ((Ortho.motion (K i)).norm_map _).symm
  rw [add_sub_add_right_eq_sub]
  change d ≤ ‖Ortho.motion (K i) (B j) - Ortho.motion (K i) (B k)‖
  rw [← map_sub,(Ortho.motion (K i)).norm_map]; exact (h.2 j k e').le

lemma multilinear_price {b : J → ℕ} (M : l → MultilinearMap ℂ (fun j : J => S.Field (b j)) ℂ)
    (hT : Tendsto T φ atTop) (x : Ortho → Slots S b) (hc : Continuous x) (K : l → Ortho)
    (he : ∀ v, RateLE φ T (fun i => M i v) κ) : RateLE φ T (fun i => M i (x (K i))) κ := by
  let f := fun j:J => Module.finBasis ℂ (S.Field (b j))
  have hq (a : ∀ j, Fin (Module.finrank ℂ (S.Field (b j)))) : Continuous (fun g:Ortho =>
      (∏ i, (f i).coord (a i) (x g i))) := continuous_finsetProd _ fun i _ =>
        ((f i).coord (a i)).continuous_of_finiteDimensional.comp ((continuous_pi_iff.mp hc) i)
  conv => arg 3; ext i; rw [decompose]
  apply RateLE.sum hT; intro a _
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hq a).continuousOn
  let v : Slots S b := fun i => f i (a i)
  exact ((RateLE.absBound (F:=fun k:l => ∏ i, (f i).coord (a i) (x (K k) i)) C hT
    (Eventually.of_forall fun k => hC _ (mem_univ (K k)))).mul (he v)).mono (zero_add _ |>.le)

-- Price signed combinations. Positions in absolute coordinates about `O i`.
section Pack
variable {B:Type} [Fintype B] (J : B → Type) [∀ b, Fintype (J b)]
  (O : l → E4) (X : (b:B) → l → J b → E4) (v : (b:B) → l → J b → S.Tag)
  (c : B → l → ℂ)

/-- Shrinking room without assumption on inner pair ratios. -/
structure Fits (φ : Filter l) : Prop where
  inch b : Tendsto (fun i => away (X b i) (O i)) φ (𝓝 (0 : J b → E4))
  inj b : ∀ᶠ i in φ, Injective (X b i)

-- Syntax Lean section params check
/-- Price with whole signed cancellation, at fixed exterior clearance. -/
structure NearProbes (φ : Filter l) (T : l → ℝ) (u : ℝ) : Prop where
  fare {I : Type} [Fintype I] (w : I → S.Tag) (y : l → I → E4) {δ : ℝ} :
    0 < δ → (∀ᶠ i in φ, ClearOf (O i) (y i) δ) → RateLE φ T (fun i =>
      ∑ b, c b i * kernel S (beside (X b i) (y i)) (beside (v b i) w)) u

variable (hT : Tendsto T φ atTop)
variable (H : Fits J O X φ) (hw : NearProbes J O X v c φ T κ)
variable {d : ℕ} (D : Prism (S:=S) (d:=d)) -- d implicit edit
open Table Survey
include H
omit [Fintype B] in
lemma Fits.sized (b : B) : ∀ᶠ i in φ, sized D (away (X b i) (O i)) := by
  have h := (H.inch b).norm
  filter_upwards [H.inj b,h.eventually (gt_mem_nhds (by simpa using gap_pos D))] with i hi ht
  exact ⟨(away_inject ..).2 hi,fun j => lt_of_le_of_lt (norm_le_pi_norm _ j) ht⟩

omit [Fintype B] in
/-- The reader is harmless after shrinking in source, no transfer of fission
terms through collisions. -/
lemma Fits.separated (b : B) {I : Type} [Fintype I] (y : l → I → E4) {δ : ℝ} (hδ : 0 < δ)
    (he : ∀ᶠ i in φ, ClearOf (O i) (y i) δ) : ∀ᶠ i in φ, Injective (beside (X b i) (y i)) := by
  filter_upwards [he,H.inj b,(H.inch b).norm.eventually (gt_mem_nhds (by simpa using hδ))] with i hi hx ht
  apply beside_distinct.mpr
  refine ⟨hx,fun j k hk => Classical.byContradiction fun e => ?_,fun j k e => ?_⟩
  · have hh := lt_of_lt_of_le hδ (hi.spread j k e); rw [hk,sub_self,norm_zero] at hh; exact lt_irrefl _ hh
  have hh : ‖X b i j-O i‖ < δ := lt_of_le_of_lt (norm_le_pi_norm (away (X b i) (O i)) j) ht
  rw [e,norm_sub_rev] at hh; exact not_lt_of_ge (hi.openSpace k) hh

variable {P : DiffPlan S} {R : S.Rotation} {ρ : S.RealSpin} (hR : R.Laws P ρ) (hs : S.Hierarchy)
include hw hT hR hs
lemma packed_shot (K : l → Ortho) : RateLE φ T (fun i =>
    ∑ b, c b i • shot R D (away (X b i) (O i)) (v b i) (K i)) κ := by
  let Y (i:l) (e:D.probes) := placements e.val (K i)
  let g (i:l) (e:D.probes) := ∑ b:B,c b i *
    kernel S (beside (away (X b i) (O i)) (Y i e)) (beside (v b i) (labelSet R e.val (K i)))
  have he (e:D.probes) : RateLE φ T (fun i=>g i e) κ := by
    let n (j:Fin e.val.n) := (e.val.letter j).fst
    let M (i:l) : MultilinearMap ℂ (fun j => S.Field (n j)) ℂ :=
      ∑ b,c b i • withExterior S (away (X b i) (O i)) (v b i) n (Y i e)
    have hj (i:l) (w : Slots S n) : M i w = ∑ b:B, c b i *
      kernel S (beside (away (X b i) (O i)) (Y i e)) (beside (v b i) (stockTag w)) := by
        unfold M; simp_rw [sum_apply, smul_apply,exterior_apply]; rfl
    have hh (w : Slots S n) : RateLE φ T (fun i => M i w) κ := by
      obtain ⟨δ,hδ,hc⟩ := RateLocations e.val K O
      apply (hw.fare (stockTag w) (fun i j => Y i e j + O i) hδ (Eventually.of_forall hc)).congr
      filter_upwards [eventually_all.mpr fun b => Fits.sized J O X H D b] with i hi
      rw [hj]
      refine Finset.sum_congr rfl fun b _ => congr_arg (c b i * ·) ?_
      have hh := kernel_shift hs.translations (beside (v b i) (stockTag w))
        (lives D (hi b) e (K i)) (O i)
      rwa [show (fun j => beside (away (X b i) (O i)) (placements e.val (K i)) j + O i) =
        beside (X b i) (fun j => Y i e j + O i) from funext fun j => by
          rcases j with j|j
          · simp [away]
          rfl] at hh
    let x (A : Ortho) : Slots S n := fun i => (labelSet R e.val A i).2
    have he := multilinear_price M hT x (continuous_pi (f:=x) fun i => hR.spin (n i)
        (S.classTokens (e.val.letter i)).2) K hh
    exact he.congr (Eventually.of_forall fun i => hj i (x (K i)))
  have hg : RateLE φ T g κ := by
    intro a ha
    filter_upwards [eventually_all.mpr fun j : D.probes => he j a ha] with i hi
    exact (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr hi
  let F := LinearMap.toContinuousLinearMap (D.decode.restrictScalars ℝ)
  let E := fun (K:Ortho) => LinearMap.toContinuousLinearMap (((R.act d K).toLinearMap).restrictScalars ℝ)
  have hec : Continuous E := linear_orbit R hR d
  have hen : Continuous (fun i => ‖E i‖) := (show Continuous (fun A : S.Field d →L[ℝ] S.Field d => ‖A‖) from continuous_norm (E:=S.Field d →L[ℝ] S.Field d)).comp hec
  obtain ⟨C,hC⟩ := (isCompact_range hen).bddAbove
  have h' := (RateLE.absBound (F:=E ∘ K) C hT (Eventually.of_forall fun i => hC (mem_range_self (K i))))
  refine ((h'.bil (u:=fun i => E (K i) (F (g i))) (hg.linear hT F) (Eventually.of_forall fun i =>
    (E (K i)).le_opNorm _)).mono (zero_add κ |>.le)).congr (Eventually.of_forall fun i => ?_)
  change R.act _ _ (D.decode (g i)) = _
  have hv : g i = ∑ b, c b i • (fun e:D.probes =>
        kernel S (beside (away (X b i) (O i)) (Y i e)) (beside (v b i) (labelSet R e.val (K i)))) := by
    ext1 e; unfold g; simp only [Finset.sum_apply]; rfl
  rw [hv,map_sum,map_sum]; simp_rw [map_smul]; rfl
end Pack
end Cov
end YM.OPE
