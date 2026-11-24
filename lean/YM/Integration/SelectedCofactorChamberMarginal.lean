import YM.Integration.SelectedCofactorPhysicalMoment
import YM.Push.BETA_TRANSPORT.Noise

/-! Signed marginal pairing on the actual product of retained and exterior gauge links. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorChamberMarginal
open Function Set Filter MeasureTheory Lattice Wilson RG
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def links (X : Set (Site n)) : Set (Edge (Site n)) := {e | e.1 ∈ X ∧ e.1 + step e.2 ∈ X}

abbrev Fields (G : Gauge) (A : Set (Edge (Site n))) := A → G.El

def sheet (G : Gauge) (A : Set (Edge (Site n))) : Measure (Fields G A) := Measure.pi fun _ => G.probHaar

instance (A : Set (Edge (Site n))) : IsProbabilityMeasure (sheet G A) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : A => G.probHaar))

instance (A : Set (Edge (Site n))) : IsFiniteMeasure (sheet G A) :=
  inferInstanceAs (IsFiniteMeasure (Measure.pi fun _ : A => G.probHaar))

instance (A : Set (Edge (Site n))) : SFinite (sheet G A) :=
  inferInstanceAs (SFinite (Measure.pi fun _ : A => G.probHaar))

def cut (G : Gauge) (A : Set (Edge (Site n))) : Config G n ≃ᵐ Fields G A × Fields G Aᶜ :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Edge (Site n) => G.El) (· ∈ A)

theorem cut_preserves (A : Set (Edge (Site n))) :
    MeasurePreserving (cut G A) (prior G n) ((sheet G A).prod (sheet G Aᶜ)) := by
  convert! measurePreserving_piEquivPiSubtypeProd (α := fun _ : Edge (Site n) => G.El)
    (fun _ => G.probHaar) (· ∈ A) using 1
  unfold sheet
  congr
  apply Subsingleton.elim

def marginal (A : Set (Edge (Site n))) (f : Config G n → E) (u : Fields G A) : E :=
  ∫ y, f ((cut G A).symm (u,y)) ∂sheet G Aᶜ

theorem marginal_env (A : Set (Edge (Site n))) {f : Config G n → E} (hf : Envelope f) :
    Envelope (marginal A f) := by
  have hm : StronglyMeasurable (fun z : Fields G A × Fields G Aᶜ => f ((cut G A).symm z)) :=
    (hf.meas.comp (cut G A).symm.measurable).stronglyMeasurable
  obtain ⟨c,hc⟩ := hf.cost
  refine ⟨hm.integral_prod_right'.measurable,c,fun u => ?_⟩
  simpa only [marginal,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := sheet G Aᶜ) (C := c) (ae_of_all _ fun y => hc ((cut G A).symm (u,y)))

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem total (A : Set (Edge (Site n))) {f : Config G n → E} (hf : Integrable f (prior G n)) :
    ∫ u, marginal A f u ∂sheet G A = ∫ U, f U ∂prior G n := by
  have h := cut_preserves (G := G) A
  have hi := (h.symm.integrable_comp_emb (cut G A).symm.measurableEmbedding).2 hf
  exact (integral_prod (fun z => f ((cut G A).symm z)) hi).symm.trans (h.symm.integral_comp' f)

theorem marginal_lower (A : Set (Edge (Site n))) {P : Config G n → ℝ} (hp : Envelope P) {a : ℝ}
    (ha : ∀ U, a ≤ P U) (u : Fields G A) : a ≤ marginal A P u := by
  have henv : Envelope (fun y : Fields G Aᶜ => P ((cut G A).symm (u,y))) :=
    ⟨hp.meas.comp ((cut G A).symm.measurable.comp (measurable_const.prodMk measurable_id)),
      hp.cost.imp fun c h y => h ((cut G A).symm (u,y))⟩
  simpa only [marginal,integral_const,probReal_univ,one_smul] using
    integral_mono (μ := sheet G Aᶜ) (integrable_const a) (henv.integrable _) (fun y => ha ((cut G A).symm (u,y)))

/-- Integrating all exterior links gives the denominator and signed numerator
on the identical retained configuration. -/
def projected (A : Set (Edge (Site n))) (P : Config G n → ℝ) (f : Config G n → E) (U : Config G n) : E :=
  let u := ((cut G A) U).1
  (marginal A P u)⁻¹ • marginal A f u

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem projected_local (X : Set (Site n)) (P : Config G n → ℝ) (f : Config G n → E) :
    LocalOn X (projected (links X) P f) := by
  intro U V h
  have he : ((cut G (links X)) U).1 = ((cut G (links X)) V).1 := funext fun e => h e.val e.property.1 e.property.2
  simp only [projected,he]

theorem projected_env (A : Set (Edge (Site n))) {P : Config G n → ℝ} {f : Config G n → E}
    (hp : Envelope P) (hf : Envelope f) {a : ℝ} (ha : 0 < a) (hl : ∀ U, a ≤ P U) :
    Envelope (projected A P f) := by
  have hP := marginal_env A hp
  have hF := marginal_env A hf
  have hm := measurable_fst.comp (cut G A).measurable
  obtain ⟨c,hc⟩ := hF.cost
  refine ⟨(hP.meas.inv.comp hm).smul (hF.meas.comp hm),a⁻¹*c,fun U => ?_⟩
  let u := ((cut G A) U).1
  have hlow := marginal_lower A hp hl u
  have hpos := ha.trans_le hlow
  change ‖(marginal A P u)⁻¹ • marginal A f u‖ ≤ _
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  exact mul_le_mul (inv_anti₀ ha hlow) (hc u) (norm_nonneg _) (inv_nonneg.mpr ha.le)

theorem pairing [CompleteSpace E] (A : Set (Edge (Site n))) {P : Config G n → ℝ} {f : Config G n → E}
    (hp : Envelope P) (hf : Envelope f) {a : ℝ} (ha : 0 < a) (hl : ∀ U, a ≤ P U) :
    (∫ U, P U • projected A P f U ∂prior G n) = ∫ U, f U ∂prior G n := by
  have hproj := projected_env A hp hf ha hl
  obtain ⟨c,hc⟩ := hp.cost
  obtain ⟨d,hd⟩ := hproj.cost
  have hE : Envelope (fun U => P U • projected A P f U) :=
    ⟨hp.meas.smul hproj.meas,c*d,fun U => (norm_smul_le ..).trans
      (mul_le_mul (hc U) (hd U) (norm_nonneg _) ((norm_nonneg _).trans (hc U)))⟩
  letI : IsFiniteMeasure (prior G n) := inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Edge (Site n) => G.probHaar)))
  have hint {g : Config G n → E} (hg : Envelope g) : Integrable g (prior G n) :=
    (integrable_const (μ := prior G n) hg.cost.choose).mono' hg.meas.aestronglyMeasurable (ae_of_all _ hg.cost.choose_spec)
  refine (total (G := G) A (f := fun U => P U • projected A P f U) (hint hE)).symm.trans ?_
  refine Eq.trans ?_ (total (G := G) A (f := f) (hint hf))
  apply integral_congr_ae
  apply ae_of_all
  intro u
  simp only [marginal,projected,MeasurableEquiv.apply_symm_apply]
  rw [integral_smul_const,smul_smul,mul_inv_cancel₀,one_smul]
  exact (ha.trans_le (marginal_lower A hp hl u)).ne'

end YM.Integration.SelectedCofactorChamberMarginal
end
