import YM.Integration.OriginalMarkedExteriorHaar

/-! The finite Gibbs refill has a literal density on all gauge links. Its
exterior marginal is taken from the actual incoming physical law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedExteriorReweight
open Lattice Wilson RG MeasureTheory SelectedCofactorChamberMarginal OriginalMarkedExteriorHaar
open scoped Classical
variable {G : Gauge} {n : Side}
local notation "Ω" => Config G n

def ratio (A : Set (Edge (Site n))) (P Q : Ω→ℝ) (u : Fields G A) : ℝ :=
  marginal A P u*(marginal A Q u)⁻¹

def density (A : Set (Edge (Site n))) (P Q : Ω→ℝ) (U : Ω) : ℝ :=
  Q U * ratio A P Q (((cut G A) U).1)

theorem bounded (A : Set (Edge (Site n))) {P Q : Ω→ℝ} (hp : Envelope P) (hq : Envelope Q)
    {a : ℝ} (ha : 0<a) (hl : ∀ U,a≤Q U) : Envelope (density A P Q) := by
  have pe := marginal_env A hp
  have qe := marginal_env A hq
  have floor (u) := marginal_lower A hq hl u
  have inv : Envelope (fun u => (marginal A Q u)⁻¹) := by
    refine ⟨qe.meas.inv,a⁻¹,fun u => ?_⟩
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (ha.le.trans (floor u)))]
    exact inv_anti₀ ha (floor u)
  have factor : Envelope (ratio A P Q) := pe.mul inv
  obtain ⟨b,hb⟩ := factor.cost
  exact hq.mul (⟨factor.meas.comp (measurable_fst.comp (cut G A).measurable),
    b,fun U => hb (((cut G A) U).1)⟩ : Envelope (fun U => ratio A P Q (((cut G A) U).1)))

private theorem slice (A : Set (Edge (Site n))) (P Q : Ω→ℝ) (f : Ω→ℂ) (u : Fields G A) :
    marginal A (fun U => (density A P Q U:ℂ)*f U) u =
      Complex.ofReal (marginal A P u)*OriginalMarkedExteriorHaar.test A Q f u := by
  let z (y : Fields G Aᶜ) := (cut G A).symm (u,y)
  calc
    _ = ∫ y,(ratio A P Q u:ℂ)*((Q (z y):ℂ)*f (z y)) ∂sheet G Aᶜ := by
      unfold marginal
      apply integral_congr_ae
      apply ae_of_all
      intro y
      dsimp only [density,z]
      rw [MeasurableEquiv.apply_symm_apply,Complex.ofReal_mul]
      ring
    _ = (ratio A P Q u:ℂ) * (∫ y,(Q (z y):ℂ)*f (z y) ∂sheet G Aᶜ) := integral_const_mul _ _
    _ = _ := by
      simp only [ratio,OriginalMarkedExteriorHaar.test,marginal,z,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_inv]
      ring

/-- A signed redraw on the entire field space, normalized by the originally
measured partition, represents the drawn-inside and true-outside law exactly. -/
theorem physical (A : Set (Edge (Site n))) {P Q : Ω→ℝ} {f : Ω→ℂ}
    (hp : Envelope P) (hq : Envelope Q) (hf : Envelope f) {a : ℝ} (ha : 0<a) (hl : ∀ U,a≤Q U) :
    average (prior G n) P (projected A Q (fun U => Q U • f U)) =
      ((∫ U,P U ∂prior G n):ℂ)⁻¹ * ∫ U,(density A P Q U:ℂ)*f U ∂prior G n := by
  letI : IsFiniteMeasure (prior G n) :=
    inferInstanceAs (IsFiniteMeasure (Measure.pi fun _ : Edge (Site n) => G.probHaar))
  have env := bounded A hp hq ha hl
  have hi : Integrable (fun U => (density A P Q U:ℂ)*f U) (prior G n) :=
    weighted_integrable env hf (prior G n)
  rw [replacement A hp hq hf ha hl]
  unfold OriginalMarkedExteriorHaar.average
  simp only [integral_complex_ofReal]
  rw [total A (hp.integrable (prior G n)),←total A hi]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun u => (slice A P Q f u).symm)

end YM.Integration.OriginalMarkedExteriorReweight

