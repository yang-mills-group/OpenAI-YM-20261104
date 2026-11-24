import YM.Integration.WilsonGaussianDeterminantVertex

/-! The physical coupling and spatial book for the Gaussian determinant vertex. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantBooks

open LocalTaylorR2 LocalTaylorR2.Pavilion Analysis
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Axial Channel Canvas Mesh Port Work.G05 Animals Itinerary Reserves Census

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
variable {F : Forest S.ratio} {P : Teller G}

open WilsonGaussianDeterminantVertex

variable {W s μ C : ℝ} {R : Rep G f} {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}

def forecast (p : ℕ) (R : Rep G f) (i : Bond f) : Port.Test T := fun _ X _ =>
  ∑ n ∈ Finset.range (p+1), (gStep R.beta)^n * coefficient n X i
    ((gStep R.beta)⁻¹ • Pavilion.pitch (Canvas.primary G) X (atEdge S i))

theorem prescribed (H : Cash W s μ L Q o C T R) (p : ℕ) (i : Bond f) :
    mosaics H p (letter i) = forecast (T := T) p R i := by
  funext F X z
  exact enrolled H p X i z

private theorem sqrtRate (G : Gauge) (L : Side) :
    Rate G L (1/2) (fun t => Real.sqrt (2 * betaF G t L)) := by
  have h := (Rate.power (G:=G) (L:=L) (a := (1/2 : ℝ))).mul_left (Real.sqrt 2)
  apply h.congr
  filter_upwards with x
  rw [Real.sqrt_mul (by norm_num : 0 ≤ (2:ℝ)), Real.sqrt_eq_rpow (betaF G x L)]

private theorem redeem {p : ℕ} {t : ℝ → ℝ} (h : Rate G L (-((p : ℝ)+1)/2) t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in atTop, ∀ (β : ℝ), 0 < β → β ≤ 2 * betaF G s L →
      |t s| ≤ ε * (gStep β)^p := by
  have small := (h.mul ((sqrtRate G L).pow p)).below (by linarith) ε hε
  filter_upwards [small] with s hs
  intro β hβ hcap
  have hmul : |t s| * (Real.sqrt β)^p ≤ ε := calc
    |t s| * (Real.sqrt β)^p ≤ |t s| * (Real.sqrt (2 * betaF G s L))^p :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hcap) p) (abs_nonneg _)
    _ = |t s * (Real.sqrt (2 * betaF G s L))^p| := by
      rw [abs_mul,abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) p)]
    _ ≤ ε := hs
  rw [gStep,inv_pow,← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos (Real.sqrt_pos.mpr hβ) p)).mpr hmul

theorem original (P : Teller G) (Q : ConnectedActivityE6.Target G P) (o : Target.Order G W)
    (v d : ℝ → ℝ) (L : Side) (hv : Rate G L (-(1/2)) v)
    (hd : Rate G L (-(1/2)) d) (hu : ∀ᶠ x : ℝ in atTop, 0 ≤ v x)
    (D : Patch) (hD : D.Branches P.bind G) (χ : Chi) (p j : ℕ) (ε : ℝ) (he : 0 < ε) :
    ∀ᶠ s in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f)
      (μ C : ℝ) (H : Cash W s μ L Q o C T R) (i : Bond f), S.patch = D →
      Kept H (H.supportP (identityLog (letter i))) (forecast (T := T) p R i) ∧
      Sees H j (v s) (d s) χ
        (fun F X z => X.farLog R o.a Q.table z (letter i) - forecast (T := T) p R i F X z)
        (ε * (gStep R.beta)^p) 1 ∧
      ∀ (F : Forest S.ratio) (X : Coat T F), X.x=s → X.width=o.K → X.manifest →
        ∀ z, |X.farLog R o.a Q.table z (letter i)| ≤ H.w (letter i) := by
  obtain ⟨t,ht,h⟩ := charged P Q o v d L hv hu D hD χ p j
  obtain ⟨b,_,_,hb⟩ := Pavilion.titular v d L o P Q p j 0 hv hd hu D hD χ
  filter_upwards [h, redeem ht he, hb] with s hs hsmall hPass
  intro c f S T R μ C H i hS
  have hbooks := hPass c f S T R μ C H hS
  refine ⟨prescribed H p i ▸ hbooks.stamp (letter i), ?_, ?_⟩
  · apply (hs c f S T R μ C H i hS).climb H _ le_rfl
    apply hsmall R.beta H.laws.intake.positive
    simpa only [H.laws.data.funds.length_eq] using H.laws.intake.window.2
  · intro F X h₁ h₂ h₃ z
    exact ((H.quotes F X h₁ h₂ h₃).2.1 (letter i) z).1

end YM.Integration.WilsonGaussianDeterminantBooks
end
