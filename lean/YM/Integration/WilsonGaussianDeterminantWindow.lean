import YM.Integration.WilsonGaussianDeterminantFull

/-! Every polynomial order of the original finite-window correction and the complete retained root tariff on the normalized determinant. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantWindow

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

open PhysicalAffineScalarLogarithm
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
  {F : Forest S.ratio} {R : Rep G f} {W s μ C : ℝ} {P : Teller G}
  {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}

open WilsonGaussianDeterminantFull WilsonGaussianDeterminantVertex
open RGLocalTaylor LocalLTE.Fan
open WilsonGaussianDeterminantRoster (model)

theorem rate (G : Gauge) (L : Side) (j m : ℕ) (η r Q γ v t : ℝ) (hγ : 0 < γ) :
    Rate G L t (fun s => windowPrice G j (radiusB s) m η r Q γ v) := by
  let a := 1+(v+1)
  let h := payE η r Q m
  exact (((swims G L t (polynomial G L j m a h) hγ a).mul_left (token j a h)).mul_left (v+1)).mul_left (Fintype.card G.ColorIndex)

theorem original (P : Teller G) (Q : ConnectedActivityE6.Target G P) (o : Target.Order G W)
    (L : Side) (D : Patch) (hD : D.Branches P.bind G) (χ : Chi) (p j : ℕ) (η : ℝ) (hη : 0<η)
    (v d : ℝ → ℝ) (hv : Rate G L (-(1/2)) v) (hd : Rate G L (-(1/2)) d)
    (hu : ∀ᶠ x : ℝ in atTop, 0≤v x) :
    ∀ᶠ s in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f)
      (μ C : ℝ) (H : Cash W s μ L Q o C T R), S.patch=D →
      ∃ w : Miniature c f → ℝ,
        Sales (radiusB s) Q.relative Q.ε (sleeve S (radiusB s) Q.halo) w (fun _ => 0)
          (betaF G s L ^ (-((p:ℝ)+1-η)/2)) ∧
        (∀ i : Bond f, Sees H j (v s) (d s) χ
          (fun F X z => weightLog H (letter i) F X z - model p R X i)
          (w (.inr (.inl i))) 1) ∧
        ∀ (F : Forest S.ratio) (X : Coat T F), X.x=s → X.width=o.K → X.manifest → X.χ=χ →
          ∀ (z : Air f G) (i : Bond f),
          Healthy (Pressure.temp X.x) (sleeve S X.B Q.halo (.inr (.inl i))) X.V →
          |Mayer.exponent H X z (identityLog (letter i))| ≤ H.w (letter i) ∧
          |fullPair X i + correction X i - seed X i - model p R X i| ≤ w (.inr (.inl i)) := by
  have h := WilsonGaussianDeterminantRoster.original P Q o L D hD χ p j η hη v d hv hd hu
  filter_upwards [h] with s hs c f S T R μ C H hS
  obtain ⟨w, hw, hj, hclear⟩ := hs c f S T R μ C H hS
  refine ⟨w,hw,hj,?_⟩
  intro F X hx hk hm hχ z i hfree
  have cash := hclear F X hx hk hm hχ z i hfree
  refine ⟨cash.1,?_⟩
  have same : X.undercurrent i = fullPair X i + correction X i - seed X i := by
    linarith only [rooted H X i hx hk hm]
  rw [← same]
  exact cash.2

end YM.Integration.WilsonGaussianDeterminantWindow
end
