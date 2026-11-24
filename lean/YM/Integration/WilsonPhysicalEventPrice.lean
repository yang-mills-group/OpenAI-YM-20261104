import YM.Integration.WilsonForwardMeasurable
import YM.Integration.ThermalRootedMoment

/-! First absolute moment of the complete signed forward defect on any
true root-supported event, allowing all simultaneous exterior flags. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalEventPrice
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Cells OPE.Therm OPE.Therm.House
open scoped Classical BigOperators Topology
variable {G : Gauge}

private theorem first {T : Type*} [MeasurableSpace T] (μ : Measure T) [IsFiniteMeasure μ]
    {f : T → ℂ} (hf : Envelope f) {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (hp : ∀ x, ‖f x‖ ≤ b)
    (rare : ‖∫ x, (‖f x‖ : ℂ) ∂μ‖^2 ≤ δ*(∫ x, ‖(‖f x‖ : ℂ)‖^2 ∂μ)) :
    ‖∫ x, f x ∂μ‖ ≤ δ*b := by
  have hF : Envelope (fun T => ‖f T‖) := by simpa only [pow_one] using SignedWeightedMoment.norm_power_env hf 1
  have h0 : 0 ≤ ∫ x, ‖f x‖ ∂μ := integral_nonneg (fun _=>norm_nonneg _)
  have hsq : (∫ x, ‖f x‖ ∂μ)^2 ≤ δ*(∫ x, ‖f x‖^2 ∂μ) := by
    simpa only [integral_complex_ofReal,Complex.norm_real,Real.norm_of_nonneg h0,Real.norm_of_nonneg (norm_nonneg _)] using rare
  have h2 : (∫ x, ‖f x‖^2 ∂μ) ≤ b*(∫ x, ‖f x‖ ∂μ) := by
    rw [←integral_const_mul]
    apply integral_mono ((SignedWeightedMoment.norm_power_env hf 2).integrable _) ((hF.integrable _).const_mul _)
    intro x
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (hp x) (norm_nonneg (f x))
  refine (norm_integral_le_integral_norm _).trans ?_
  have h := hsq.trans (mul_le_mul_of_nonneg_left h2 hδ)
  by_contra! z
  nlinarith only [h,mul_pos (sub_pos.mpr z) ((mul_nonneg hδ hb).trans_lt z)]

/-- Full signed model and fine input stay paired on all configurations. A
bounded coarse root selector leaves all exterior fields free. -/
theorem paired {C : Family G} (hC : C.Makes) (hG : G.Simple) (θ : Poetry C.path.levels) :
    ∀ᶠ m : ℕ in atTop, ∀ (N : ℕ), m<N → ∀ (p : ℕ) (X : Finset (Site (C.side m p)))
      (g : Config G (C.side (m+1) p) → ℂ) (model t : Config G (C.side m p) → ℂ),
      Envelope g → Envelope model → Envelope t → (∀ W, ‖t W‖ ≤ 1) →
      (∀ W, t W ≠ 0 → ∃ z ∈ X,z ∈ flags (cool C.path.levels m) W) →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → (∀ U, ‖g U‖ ≤ A) → (∀ W, ‖model W‖ ≤ B) →
      ‖∫ W,t W*(actualAverage C (N:=N) g W-model W) ∂scene C.path N p m‖ ≤
        (((X.card*(Fintype.card PlaqAxes*4):ℕ):ℝ)*vanishP C.path.levels m)*(A+B) := by
  filter_upwards [ThermalRootedMoment.rare_scene hC.wilson θ hG] with m h
  intro N hm p X g v t hg hv ht h1 fire A B hA hB gp vp
  haveI := probability (H:=C.path) (p:=p) hC.wilson hm.le
  let f (W : Config G (C.side m p)) := t W*(actualAverage C (N:=N) g W-v W)
  have hf : Envelope f := ht.mulC ((WilsonForwardMeasurable.average hC hm hg).subC hv)
  have hn : Envelope (fun W => (‖f W‖ : ℂ)) := Envelope.ofReal_env (by simpa only [pow_one] using SignedWeightedMoment.norm_power_env hf 1)
  have hp (W : Config G (C.side m p)) : ‖f W‖ ≤ A+B := by
    unfold f
    rw [norm_mul]
    exact (mul_le_mul (h1 W) ((norm_sub_le ..).trans (add_le_add (actualAverage_norm_le C hC hm gp W) (vp W))) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have root_support (W : Config G (C.side m p)) (hw : (‖f W‖:ℂ) ≠ 0) : ∃ z ∈ X,z ∈ flags (cool C.path.levels m) W := by
    apply fire W
    intro hz
    exact hw (by simp [f,hz])
  exact first (scene C.path N p m) hf (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le) (add_nonneg hA hB) hp (h N hm.le p X _ hn root_support)

end YM.Integration.WilsonPhysicalEventPrice
