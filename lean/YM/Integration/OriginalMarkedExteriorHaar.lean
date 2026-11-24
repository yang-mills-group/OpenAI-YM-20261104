import YM.Integration.SelectedCofactorChamberMarginal

/-! Integrate an actual finite gauge density after fixing its retained gauge
coordinates. The result uses its own exterior marginal and partition. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedExteriorHaar
open Lattice Wilson RG MeasureTheory SelectedCofactorChamberMarginal
open scoped Classical
variable {G : Gauge} {n : Side}
local notation "Ω" => Config G n

def average {X : Type*} [MeasurableSpace X] (μ : Measure X) (P : X→ℝ) (f : X→ℂ) : ℂ :=
  ((∫ u,P u ∂μ):ℂ)⁻¹ * ∫ u,(P u:ℂ)*f u ∂μ

def test (A : Set (Edge (Site n))) (Q : Ω→ℝ) (f : Ω→ℂ) (u : Fields G A) : ℂ :=
  (marginal A Q u)⁻¹ • marginal A (fun U => Q U • f U) u

theorem weighted {X : Type*} [MeasurableSpace X] {P : X→ℝ} {f : X→ℂ}
    (p : Envelope P) (h : Envelope f) : Envelope (fun u => P u • f u) := by
  obtain ⟨c,hc⟩ := p.cost
  obtain ⟨b,hb⟩ := h.cost
  exact ⟨p.meas.smul h.meas,c*b,fun u => (norm_smul_le ..).trans
    (mul_le_mul (hc u) (hb u) (norm_nonneg _) ((norm_nonneg _).trans (hc u)))⟩

theorem weighted_integrable {X : Type*} [MeasurableSpace X] {P : X→ℝ} {f : X→ℂ}
    (hp : Envelope P) (hf : Envelope f) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable (fun u => (P u:ℂ)*f u) μ := by
  have h := weighted hp hf
  obtain ⟨c,hc⟩ := h.cost
  simpa only [Complex.real_smul] using
    (Integrable.of_bound (μ := μ) h.meas.aestronglyMeasurable c (ae_of_all _ hc))

theorem test_env (A : Set (Edge (Site n))) {Q : Ω→ℝ} {f : Ω→ℂ}
    (hq : Envelope Q) (hf : Envelope f) {a : ℝ} (ha : 0<a) (hl : ∀ U,a≤Q U) : Envelope (test A Q f) := by
  let K := projected A Q (fun U => Q U • f U)
  let lift (u : Fields G A) := (cut G A).symm (u,(1 : Fields G Aᶜ))
  have hm : Measurable lift := (cut G A).symm.measurable.comp (measurable_id.prodMk measurable_const)
  have env : Envelope K := projected_env A hq (weighted hq hf) ha hl
  have e : test A Q f=fun u => K (lift u) := by
    funext u
    simp only [test,K,lift,projected,MeasurableEquiv.apply_symm_apply]
  obtain ⟨b,hb⟩ := env.cost
  rw [e]
  exact ⟨env.meas.comp hm,b,fun u => hb (lift u)⟩

/-- The exterior mean is taken against the actual marginal of P, whose total
mass equals the original full partition. -/
theorem exterior (A : Set (Edge (Site n))) {P : Ω→ℝ} (hp : Envelope P)
    {F : Fields G A→ℂ} (hf : Envelope F) :
    average (prior G n) P (fun U => F (((cut G A) U).1)) =
      average (sheet G A) (marginal A P) F := by
  letI : IsFiniteMeasure (prior G n) :=
    inferInstanceAs (IsFiniteMeasure (Measure.pi fun _ : Edge (Site n) => G.probHaar))
  let f (U : Ω) := F (((cut G A) U).1)
  obtain ⟨b,hb⟩ := hf.cost
  have fe : Envelope f := ⟨hf.meas.comp (measurable_fst.comp (cut G A).measurable),
    b,fun U => hb (((cut G A) U).1)⟩
  have integ : Integrable (fun U => (P U:ℂ)*f U) (prior G n) :=
    weighted_integrable hp fe (prior G n)
  have mEq := (total (G:=G) A (hp.integrable (prior G n))).symm
  have nEq := (total (G:=G) A integ).symm
  unfold average
  change ((∫ U,P U ∂prior G n):ℂ)⁻¹*(∫ U,(P U:ℂ)*f U ∂prior G n)=_
  simp only [integral_complex_ofReal]
  rw [mEq,nEq]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro u
  simp only [marginal,f,MeasurableEquiv.apply_symm_apply,integral_mul_const,integral_complex_ofReal]

/-- Apply the conditional law of Q to the inside, and retain the full
posterior P on the outside. Both genuine densities and the two integrations
are explicit. -/
theorem replacement (A : Set (Edge (Site n))) {P Q : Ω→ℝ} {f : Ω→ℂ}
    (hp : Envelope P) (hq : Envelope Q) (hf : Envelope f) {a : ℝ} (ha : 0<a) (hl : ∀ U,a≤Q U) :
    average (prior G n) P (projected A Q (fun U => Q U • f U)) =
      average (sheet G A) (marginal A P) (test A Q f) :=
  exterior A hp (test_env A hq hf ha hl)

theorem own (A : Set (Edge (Site n))) {Q : Ω→ℝ} {f : Ω→ℂ}
    (hq : Envelope Q) (hf : Envelope f) {a : ℝ} (ha : 0<a) (hl : ∀ U,a≤Q U) :
    average (prior G n) Q f=average (sheet G A) (marginal A Q) (test A Q f) := by
  have e : average (prior G n) Q (projected A Q (fun U => Q U • f U))=average (prior G n) Q f := by
    unfold average
    apply congrArg (((∫ U,Q U ∂prior G n):ℂ)⁻¹ * ·)
    simpa only [Complex.real_smul] using pairing A hq (weighted hq hf) ha hl
  exact e.symm.trans (replacement A hq hq hf ha hl)

end YM.Integration.OriginalMarkedExteriorHaar

