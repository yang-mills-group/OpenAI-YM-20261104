import YangMills.WilsonProof.NativeSupport.ActualNearBonds

/-! Exact full-layer cancellation at the identity for a difference of two
fine observables related by a translation of the terminal lattice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open Function Finset MeasureTheory Lattice Wilson RG RGComparison.Core16
open WilsonUniformUnmarkedInletEnergySites WilsonUniformUnmarkedInletConnectedShift
open WilsonUniformUnmarkedInletBondCovariances WilsonUniformUnmarkedInletBondRemainder
open scoped Classical BigOperators
variable {G : Gauge} {n c : Side}

def liftSite {n : Side} : {c : Side} → Descent n c → Site c → Site n
  | _, .nil => id
  | _, .push S _ d => liftSite d ∘ S.ratio.embed

private lemma step_pull (A : Levels G) (i p : ℕ) (β : ℝ) (b : Site (A.S.side i p))
    (f : Config G (A.S.side (i+1) p) → ℝ) (hf : Integrable f (prior G _))
    (V : Config G (A.S.side i p)) :
    let S := A.clock.op i p
    S.push β f (pull 1 b V) = S.push β (fun U => f (pull 1 (S.ratio.embed b) U)) V := by
  intro S
  let k := pull (1 : Signed) (S.ratio.embed b) (K := G.El)
  let μ : Measure (Config G (A.S.side (i+1) p)) := prior G _
  have hk : MeasurePreserving k μ μ := prior_pull ..
  let F (U) := S.density β U (pull 1 b V) • f U
  have hi : ∫ U, F U ∂μ = ∫ U, F (k U) ∂μ := by
    have hF : AEStronglyMeasurable F (Measure.map k μ) := by
      rw [hk.map_eq]
      exact (StepData.push_slice (A.transition_mass ..) _ _ hf).aestronglyMeasurable
    rw [← integral_map hk.aemeasurable hF, hk.map_eq]
  change (∫ U, F U ∂μ) = ∫ U, S.density β U V • f (k U) ∂μ
  rw [hi]
  exact integral_congr_ae (.of_forall fun U =>
    congrArg (· • f (k U)) ((A.blocks i p).symmetric β U V 1 b))

private lemma output_pull {A : Levels G} {p N t : ℕ} (T : Slices A p) (h : t ≤ N)
    (β : ℕ → ℝ) (f : Config G (A.S.side N p) → ℝ) (hf : Integrable f (prior G _))
    (b : Site (A.S.side t p)) (V : Config G (A.S.side t p)) :
    let d := traversal T h
    d.output β f (pull 1 b V) = d.output β (fun U => f (pull 1 (liftSite d b) U)) V := by
  dsimp only
  induction h using Nat.decreasingInduction generalizing β with
  | self => rw [traversal_self]; rfl
  | of_succ i hi ih =>
    rw [traversal_push T hi, Descent.output_push, Descent.output_push, step_pull A i p]
    · apply congrArg (fun u => (A.clock.op i p).push (β 1) u V)
      funext U
      exact ih (Descent.upβ β) ((A.clock.op i p).ratio.embed b) U
    · exact Descent.output_integrable (traversal_ok T hi) _ hf

private lemma output_sub (d : Descent n c) (h : d.OK G) (β : ℕ → ℝ)
    (f k : Config G n → ℝ) (hf : Integrable f (prior G _)) (hk : Integrable k (prior G _)) :
    d.output β (f-k) = d.output β f - d.output β k := by
  induction d generalizing β with
  | nil => rfl
  | push S T d ih =>
    rw [Descent.output_push, Descent.output_push, Descent.output_push, ih h.2]
    funext V
    unfold StepData.push
    simp only [Pi.sub_apply, smul_sub]
    exact integral_sub (StepData.push_slice (S.isKernel h.1 _) _ _ (Descent.output_integrable h.2 _ hf))
      (StepData.push_slice (S.isKernel h.1 _) _ _ (Descent.output_integrable h.2 _ hk))

theorem translated_read {A : Levels G} {p N t : ℕ} (T : Slices A p) (h : t ≤ N)
    (b : Site (A.S.side t p)) (f : Config G (A.S.side N p) → ℝ) (hf : Continuous f)
    (β : ℕ → ℝ) :
    let d := traversal T h
    d.conditioned β (fun U => f (pull 1 (liftSite d b) U) - f U) 1 = 0 := by
  intro d
  let w : Config G (A.S.side N p) → ℝ := bare (β d.depth)
  let a := liftSite d b
  let k := pull (1 : Signed) a (K := G.El)
  let F := w • f
  have hF : Continuous F := (bare_cont _).smul hf
  have hF' : Continuous (F ∘ k) := hF.comp (continuous_pull ..)
  have integrableF : Integrable F (prior G _) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have eqF := output_pull T h β F integrableF b (1 : Config G _)
  have unit : pull (1 : Signed) b (1 : Config G _) = 1 := by rw [pull_one]; rfl
  rw [unit] at eqF
  have diff : w • (fun U => f (k U) - f U) = F ∘ k - F := by
    funext U
    change bare (β d.depth) U * (f (pull 1 a U) - f U) =
      bare (β d.depth) (pull 1 a U) * f (pull 1 a U) - bare (β d.depth) U * f U
    rw [bare_pull, mul_sub]
  change (d.vacuum β 1)⁻¹ • d.output β (w • (fun U => f (k U) - f U)) 1 = 0
  rw [diff, output_sub d (traversal_ok T h) β _ _
    (hF'.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) integrableF]
  change (d.vacuum β 1)⁻¹ • (d.output β (F ∘ k) 1 - d.output β F 1) = 0
  rw [show d.output β (F ∘ k) 1 = d.output β F 1 from eqF.symm, sub_self, smul_zero]

theorem translated_layer {A : Levels G} {p N t : ℕ} (T : Slices A p) (h : t ≤ N)
    (b : Site (A.S.side t p)) (f : Config G (A.S.side N p) → ℝ) (hf : Continuous f)
    (β v : ℕ → ℝ) (r : ℝ) (j : ℕ) :
    let d := traversal T h
    let φ := fun U => f (pull 1 (liftSite d b) U) - f U
    GaugeInvariant φ → j < d.depth →
      ∑ q ∈ (interior d).filter (fun q => lag d q = j), picture d β v 1 φ r q = 0 := by
  intro d φ symm hj
  let Y := temperatures β v r
  let e := fun i : ℕ => if i = j then (1 : ℝ) else 0
  have endValue : e d.depth = 0 := if_neg (Nat.ne_of_gt hj)
  have test : Continuous φ := (hf.comp (continuous_pull ..)).sub hf
  have flat (s : ℝ) : d.conditioned (temperatures Y e s) φ 1 = 0 :=
    translated_read T h b f hf _
  have nul : HasDerivAt (fun s => d.conditioned (temperatures Y e s) φ 1) 0 0 := by
    simpa only [flat] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have z := (derivative d (traversal_ok T h) Y e 1 test symm 0).unique nul
  rw [WilsonUniformUnmarkedInletBondCovariances.centered d (traversal_ok T h) Y e endValue 1 test 0] at z
  rw [Finset.sum_filter]
  convert z using 1
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : lag d q = j
  · simp only [hq, e, if_true, one_mul]
    unfold picture
    have eqY : temperatures Y e 0 = Y := by funext i; simp [temperatures, WilsonUniformUnmarkedInletSignedResponse.line]
    rw [eqY]
  · simp [e, hq]

end YM.Integration.InletSusceptibility
