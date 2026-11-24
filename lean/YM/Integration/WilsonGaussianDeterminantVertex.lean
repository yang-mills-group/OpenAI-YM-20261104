import YM.LocalTaylorR2.Pavilion.Sheets

/-! The Gaussian determinant occurring on the elastic physical logarithm roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantVertex

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

def letter (i : Bond f) : LogIndex c f := .inr (.inl (.inr (.inl i)))

theorem realLog (X : Coat T F) (R : Rep G f) (a : ℝ) (Ñ : ChartRatio G) (z : Air f G)
    (i : Bond f) :
    X.farLog R a Ñ z (letter i) =
      if voyage X.seeds (200 * X.B) i then 0 else
        (Batch.joint X.blank.plate X.shutter i - Batch.joint X.plate X.shutter i)/2 := rfl

def coefficient (n : ℕ) (X : Coat T F) (i : Bond f) (v : ZipP G c f) : ℝ :=
  if voyage X.seeds (200 * X.B) i then 0 else
    Tensor.diagonal (Tensor.coeff (Pavilion.stag X i) n 0) v

theorem polynomial (p : ℕ) (X : Coat T F) (i : Bond f) (v : ZipP G c f) (g : ℝ) :
    (if voyage X.seeds (200 * X.B) i then 0 else
      blockTaylor p (Pavilion.stag X i) (g • v)) =
      ∑ n ∈ Finset.range (p+1), g^n * coefficient n X i v := by
  classical
  by_cases h : voyage X.seeds (200 * X.B) i
  · simp [coefficient,h]
  simp only [coefficient,if_neg h,blockTaylor,Finset.sum_apply]
  exact Finset.sum_congr rfl fun n _ => Tensor.homogeneous _ v g

theorem named (p : ℕ) (X : Coat T F) (i : Bond f) (g : ℝ) (hg : g ≠ 0) :
    gainV p X i = ∑ n ∈ Finset.range (p+1), g^n *
      coefficient n X i (g⁻¹ • Pavilion.pitch (Canvas.primary G) X (atEdge S i)) := by
  have h := polynomial p X i (g⁻¹ • Pavilion.pitch (Canvas.primary G) X (atEdge S i)) g
  simpa only [gainV, smul_smul, mul_inv_cancel₀ hg, one_smul] using h

variable {W s μ C : ℝ} {R : Rep G f} {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}

theorem enrolled (H : Cash W s μ L Q o C T R) (p : ℕ) (X : Coat T F) (i : Bond f) (z : Air f G) :
    mosaics H p (letter i) F X z = ∑ n ∈ Finset.range (p+1), (gStep R.beta)^n *
      coefficient n X i ((gStep R.beta)⁻¹ • Pavilion.pitch (Canvas.primary G) X (atEdge S i)) := by
  exact named p X i _ (inv_pos.mpr (Real.sqrt_pos.mpr H.laws.intake.positive)).ne'

theorem charged (P : Teller G) (Q : ConnectedActivityE6.Target G P) (o : Target.Order G W)
    (v d : ℝ → ℝ) (L : Side) (V : Rate G L (-(1/2)) v) (he : ∀ᶠ x : ℝ in atTop, 0 ≤ v x)
    (D : Patch) (hD : D.Branches P.bind G) (χ : Chi) (p j : ℕ) :
    ∃ t, Rate G L (-((p : ℝ)+1)/2) t ∧ ∀ᶠ s in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f) (μ C : ℝ)
      (H : Cash W s μ L Q o C T R) (i : Bond f), S.patch = D →
      Sees H j (v s) (d s) χ (fun _ X z => X.farLog R o.a Q.table z (letter i) -
        ∑ n ∈ Finset.range (p+1), (gStep R.beta)^n * coefficient n X i
          ((gStep R.beta)⁻¹ • Pavilion.pitch (Canvas.primary G) X (atEdge S i))) |t s| 1 := by
  obtain ⟨t,ht,h⟩ := storesD P Q o v d L V he D hD χ p j
  refine ⟨t, ht, ?_⟩
  filter_upwards [h] with s hs
  intro c f S T R μ C H i hS
  have hβ : gStep R.beta ≠ 0 := (inv_pos.mpr (Real.sqrt_pos.mpr H.laws.intake.positive)).ne'
  convert hs c f S T R μ C H i hS using 1
  funext F X z
  exact congrArg (fun value => X.undercurrent i - value) (named p X i _ hβ).symm

end YM.Integration.WilsonGaussianDeterminantVertex
end
