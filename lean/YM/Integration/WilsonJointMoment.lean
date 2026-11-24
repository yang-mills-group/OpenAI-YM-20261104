import YM.Integration.ActualNormalizedPush
import YM.Integration.SignedWeightedMoment
import YM.Integration.WilsonSpectatorReflection
import YM.Push.SECTOR_MEASURE.Decompose

/-! Forward conditional moments of a single complete signed fine field
against its genuine coarse model and selected coarse event. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonJointMoment

open Function Finset Set MeasureTheory Lattice Wilson RG
open Push.GridApprox SignedWeightedMoment
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {N p m : ℕ}
local notation "nf" => C.side (m+1) p
local notation "nc" => C.side m p
local notation "Pf" => C.path.rep N p (m+1)
local notation "Pc" => C.path.rep N p m
local notation "K" => C.path.levels.clock.op m p
local notation "b" => C.path.β N p (m+1)

private theorem kernel_slice {c f : Side} (S : StepData c f) {β : ℝ} (h : S.IsKernel β G) (V : Config G c) :
    Envelope (fun U : Config G f => S.density β U V) := by
  have hpair : Measurable (fun U : Config G f => (U,V)) := measurable_id.prodMk measurable_const
  exact Envelope.comp_env (f:=fun Z : Config G f × Config G c => S.density β Z.1 Z.2)
    (g:=fun U : Config G f => (U,V)) (den_env h) hpair

private theorem normalized_env {T : Type*} [MeasurableSpace T] {a w : T→ℝ} (ha : Envelope a) (hw : Envelope w) (v : ℝ) :
    Envelope (fun T => a T*w T/v) := by
  simpa only [div_eq_mul_inv] using (ha.mul hw).mul (Envelope.const v⁻¹)

private theorem conditional_env (hC : C.Makes) (hm : m<N) (V : Config G nc) :
    Envelope (actualConditionalDensity C N p m V) :=
  normalized_env (kernel_slice (K) (C.path.levels.transition_mass m p b) V)
    ((Pf).envelope (hC.wilson.represents N p (m+1) hm).good) ((Pc).eval V)

/-- Conditional Jensen retains the signed difference with the actual coarse
model inside the integral, before taking a norm. -/
theorem conditional (hC : C.Makes) (hm : m<N) {g : Config G nf → ℂ} (hg : Envelope g)
    (V : Config G nc) (q : ℂ) (k : ℕ) :
    ‖actualAverage C (N:=N) g V-q‖^k ≤
      ∫ U, actualConditionalDensity C N p m V U * ‖g U-q‖^k ∂prior G nf := by
  letI : IsFiniteMeasure (prior G nf) := inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Edge (Site nf) => G.probHaar)))
  let f := actualConditionalDensity C N p m V
  have he : Envelope f := conditional_env hC hm V
  have hy : (∫ T, f T ∂prior G nf) = 1 := actualConditionalDensity_total C hC hm V
  have hp : 0 < ∫ T, f T ∂prior G nf := hy.symm ▸ zero_lt_one
  have hq := jensen (prior G nf) he (actualConditionalDensity_nonneg C hC hm V) hp (hg.subC (Envelope.constC q)) k
  have hA : (∫ U, f U • (g U-q) ∂prior G nf) = actualAverage C (N:=N) g V-q := by
    simp only [smul_sub]
    rw [integral_sub (Push.SectorMeasure.Env.smul_L1 he (hg.integrableC _)) ((he.integrable _).smul_const q),integral_smul_const,hy,one_smul]
    rfl
  simpa only [hy,inv_one,one_mul,one_smul,hA] using hq

/-- Forward physical disintegration for a genuine bounded coarse event and
model. The single fine field and the full signed model remain paired in
the actual adjacent Wilson coupling throughout the right side. -/
theorem joint (hC : C.Makes) (hm : m<N) {g : Config G nf → ℂ} (hg : Envelope g)
    {model : Config G nc → ℂ} (hmodel : Envelope model) {t : Config G nc → ℝ} (ht : Envelope t)
    (ht0 : ∀ V, 0 ≤ t V) (k : ℕ) :
    (∫ V, (Pc).eval V*t V*‖actualAverage C (N:=N) g V-model V‖^k ∂prior G nc) ≤
      ∫ U, (Pf).eval U * ∫ V, (K).density b U V*t V*‖g U-model V‖^k ∂prior G nc ∂prior G nf := by
  letI : IsFiniteMeasure (prior G nf) := inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Edge (Site nf) => G.probHaar)))
  letI : IsFiniteMeasure (prior G nc) := inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Edge (Site nc) => G.probHaar)))
  let J (U : Config G nf) (V : Config G nc) := (Pf).eval U*((K).density b U V*t V*‖g U-model V‖^k)
  have hW := (C.path.rep N p (m+1)).envelope (hC.wilson.represents N p (m+1) hm).good
  have hf : Envelope (fun z : Config G nf × Config G nc => g z.1-model z.2) :=
    (hg.comp_env measurable_fst).subC (hmodel.comp_env measurable_snd)
  have hj : Envelope (fun z : Config G nf × Config G nc => J z.1 z.2) :=
    (hW.comp_env measurable_fst).mul (((den_env (C.path.levels.transition_mass m p b)).mul
      (ht.comp_env measurable_snd)).mul (norm_power_env hf k))
  have hl (V : Config G nc) : (Pc).eval V*t V*‖actualAverage C (N:=N) g V-model V‖^k ≤
      ∫ U, J U V ∂prior G nf := by
    have h0 := Multi.AxisShift.chosen_positive hC.wilson hm.le V
    refine (mul_le_mul_of_nonneg_left (conditional hC hm hg V (model V) k) (mul_nonneg h0.le (ht0 V))).trans_eq ?_
    rw [←integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro U
    change (Pc).eval V*t V*((K).density b U V*(Pf).eval U/(Pc).eval V*‖g U-model V‖^k) = J U V
    dsimp only [J]
    field_simp [h0.ne']
  calc _ ≤ ∫ V, ∫ U, J U V ∂prior G nf ∂prior G nc := integral_mono_of_nonneg
         (ae_of_all _ fun V => mul_nonneg (mul_nonneg (Multi.AxisShift.chosen_positive hC.wilson hm.le V).le (ht0 V)) (pow_nonneg (norm_nonneg _) _))
         ((Push.SectorMeasure.Env.marginal hj (prior G nf)).integrable _) (ae_of_all _ hl)
       _ = ∫ U, ∫ V, J U V ∂prior G nc ∂prior G nf := (integral_integral_swap
         (μ:=prior G nf) (ν:=prior G nc) (f:=J) (hj.integrable _)).symm
       _ = _ := by
         apply integral_congr_ae
         exact ae_of_all _ fun U => integral_const_mul _ _

end YM.Integration.WilsonJointMoment
