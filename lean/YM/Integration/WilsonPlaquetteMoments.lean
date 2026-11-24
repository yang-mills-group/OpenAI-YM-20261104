import YM.Integration.WilsonCurvatureRankRate
import YM.Integration.WilsonWeakStepPairing
import YM.Next.FLUCTUATIONS.Charts

/-! Moments of one original plaquette and their transfer to arbitrary bounded outgoing tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPlaquetteMoments
open Filter MeasureTheory Set Lattice Wilson RG OPE.Therm Push.GridApprox
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

theorem split (z : Face (Per n)) (q : ℕ) {t : ℝ} (ht : 0 ≤ t) (U : Config G n) :
    (G.chord (faceValue U z))^q ≤ t^q+2^q*WilsonCurvatureEndpoints.hit z t U := by
  by_cases h : U ∈ trigger z t
  · rw [WilsonCurvatureEndpoints.hit,Set.indicator_of_mem h,mul_one]
    exact (pow_le_pow_left₀ (G.chord_nonneg _) (G.chord_le_two _) q).trans (le_add_of_nonneg_left (pow_nonneg ht q))
  · rw [WilsonCurvatureEndpoints.hit,Set.indicator_of_notMem h,mul_zero,add_zero]
    exact pow_le_pow_left₀ (G.chord_nonneg _) (le_of_not_gt h) q

theorem weighted (μ : Measure (Config G n)) [IsProbabilityMeasure μ] (z : Face (Per n)) (q : ℕ)
    {t δ M : ℝ} (ht : 0 ≤ t) (hδ : μ.real (trigger z t) ≤ δ) (hM : 0 ≤ M)
    (v : Config G n → ℝ) (hv : ∀ U, 0 ≤ v U) (h : ∀ U,v U ≤ M*(G.chord (faceValue U z))^q) :
    (∫ U,v U ∂μ) ≤ M*(t^q+2^q*δ) := by
  let I := WilsonCurvatureEndpoints.hit (G:=G) z t
  have hI : Integrable I μ := (integrable_const _).indicator (fire_meas _ _)
  have he : (∫ U,I U ∂μ) ≤ δ := by
    change (∫ U,(trigger z t).indicator (fun _ : Config G n => (1:ℝ)) U ∂μ) ≤ δ
    rwa [integral_indicator (fire_meas _ _),setIntegral_const,smul_eq_mul,mul_one]
  calc
    _ ≤ ∫ U,M*(t^q+2^q*I U) ∂μ := integral_mono_of_nonneg (ae_of_all _ hv)
      (((integrable_const _).add (hI.const_mul _)).const_mul _)
      (ae_of_all _ fun U => (h U).trans (mul_le_mul_of_nonneg_left (split _ _ ht U) hM))
    _ = M*(t^q+2^q*∫ U,I U ∂μ) := by
      rw [integral_const_mul,integral_add (integrable_const _) (hI.const_mul _),integral_const,
        probReal_univ,one_smul,integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add_right (mul_le_mul_of_nonneg_left he (by positivity)) _) hM

theorem matrix (μ : Measure (Config G n)) [IsProbabilityMeasure μ] (z : Face (Per n)) (q : ℕ)
    {t δ : ℝ} (ht : 0 ≤ t) (hδ : μ.real (trigger z t) ≤ δ) :
    (∫ U, ‖G.mat (faceValue U z)-1‖^q ∂μ) ≤ G.colorScale^q*(t^q+2^q*δ) := by
  apply weighted μ z q ht hδ (pow_nonneg G.colorScale_pos.le q) _ (fun _ => by positivity)
  intro U
  rw [← Next.Fluctuations.chord_dist,mul_pow]

theorem original {H : History G} (Y : H.Selected) (P : Poetry H.levels) (hG : G.Simple)
    (q : ℕ) {s : ℝ} (hs : s < q) : ∀ᶠ m : ℕ in atTop, ∀ N, m ≤ N → ∀ p,
    ∀ z : Face (Per (H.S.side m p)),
      (∫ U, ‖G.mat (faceValue U z)-1‖^q ∂scene H N p m) ≤
        G.colorScale^q*((1+2^q)*(H.levels.clock.hatCoupling m)^s) := by
  filter_upwards [rare P hG Y,WilsonCurvatureRankRate.thermal H.levels hG q hs] with m hr h
  intro N hm p z
  letI : IsProbabilityMeasure (scene H N p m) := probability (H:=H) (p:=p) Y hm
  apply (matrix _ z q h.1 (hr N hm p z)).trans (mul_le_mul_of_nonneg_left _ (pow_nonneg G.colorScale_pos.le q))
  rw [add_mul,one_mul]
  exact add_le_add h.2.1 (mul_le_mul_of_nonneg_left h.2.2 (by positivity))

variable {C : Family G} {m N p : ℕ}
local notation "nf" => C.side (m+1) p
local notation "nc" => C.side m p
local notation "μc" => scene C.path N p m
local notation "μf" => scene C.path N p (m+1)
local notation "op" => C.path.levels.clock.op m p
local notation "b" => C.path.β N p (m+1)

theorem transfer (hC : C.Makes) (hm : m<N) (z : Face (Per nf)) (q : ℕ)
    {t δ M : ℝ} (ht : 0 ≤ t) (hδ : (μf).real (trigger z t) ≤ δ) (hM : 0 ≤ M)
    (f : Config G nf → ℂ) (hf : Measurable f) (h : ∀ U, ‖f U‖ ≤ M*(G.chord (faceValue U z))^q)
    (ζ : Config G nc → ℂ) (hz : Measurable ζ) (hζ : ∀ W,‖ζ W‖ ≤ 1) :
    ‖∫ W, actualAverage C (N:=N) f W * ζ W ∂μc‖ ≤ M*(t^q+2^q*δ) := by
  letI : IsProbabilityMeasure μf := probability (H:=C.path) (p:=p) hC.wilson hm
  have Ef : Envelope f := ⟨hf,M*2^q,fun U => (h U).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (G.chord_nonneg _) (G.chord_le_two _) q) hM)⟩
  rw [WilsonWeakStepPairing.forward hC hm (show Envelope ζ from ⟨hz,1,hζ⟩) Ef]
  apply (norm_integral_le_integral_norm _).trans (weighted μf z q ht hδ hM _ (fun _ => norm_nonneg _) _)
  intro U
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (back_bound (C.path.levels.transition_mass m p b) hz 1 hζ U)).trans (h U)

theorem tested (hC : C.Makes) (P : Poetry C.path.levels) (hG : G.Simple) (q : ℕ) {s : ℝ} (hs : s < q) :
    ∀ᶠ m : ℕ in atTop, ∀ N, m<N → ∀ p, ∀ z : Face (Per (C.side (m+1) p)),
    ∀ M : ℝ, 0 ≤ M → ∀ f : Config G (C.side (m+1) p) → ℂ, Measurable f →
      (∀ U, ‖f U‖ ≤ M*(G.chord (faceValue U z))^q) →
      ∀ ζ : Config G (C.side m p) → ℂ, Measurable ζ → (∀ W,‖ζ W‖ ≤ 1) →
      ‖∫ W, actualAverage C (N:=N) f W * ζ W ∂scene C.path N p m‖ ≤
        M*((1+2^q)*(C.path.levels.clock.hatCoupling (m+1))^s) := by
  obtain ⟨k,hk⟩ := eventually_atTop.mp ((rare P hG hC.wilson).and (WilsonCurvatureRankRate.thermal C.path.levels hG q hs))
  filter_upwards [eventually_ge_atTop k] with m hm
  intro N hN p z M hM f hf h ζ hz hζ
  have e := hk (m+1) (by omega)
  apply (transfer hC hN z q e.2.1 (e.1 N hN p z) hM f hf h ζ hz hζ).trans
    (mul_le_mul_of_nonneg_left _ hM)
  rw [add_mul,one_mul]
  exact add_le_add e.2.2.1 (mul_le_mul_of_nonneg_left e.2.2.2 (by positivity))

end YM.Integration.WilsonPlaquetteMoments
end
