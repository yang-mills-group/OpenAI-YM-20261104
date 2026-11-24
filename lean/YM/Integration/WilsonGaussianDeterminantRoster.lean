import YM.Integration.WilsonGaussianDeterminantResolvent
import YM.Integration.WilsonRetainedMiniatureRoot

/-! One original rooted receipt for the independent finite Gaussian determinant coefficients on the physical low roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantRoster

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


open WilsonGaussianDeterminantResolvent RGLocalTaylor

def model (p : ℕ) (R : Rep G f) (X : Coat T F) (i : Bond f) : ℝ :=
  ∑ n ∈ Finset.range (p+1), (gStep R.beta)^n * reading n X i
    ((gStep R.beta)⁻¹ • Pavilion.pitch (Canvas.primary G) X (atEdge S i))

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
          |Mayer.exponent H X z (identityLog (letter i)) - model p R X i| ≤ w (.inr (.inl i)) := by
  have whole := WilsonRetainedMiniatureRoot.original P Q o L D hD χ p j η hη v d hv hd hu
  have read := WilsonGaussianDeterminantResolvent.paid P Q o v L hv hu D hD p
  filter_upwards [whole,read] with s hwhole hread
  intro c f S T R μ C H hS
  obtain ⟨w,hs,hj,hw⟩ := hwhole c f S T R μ C H hS
  have eq (F : Forest S.ratio) (X : Coat T F) (hx : X.x=s) (hk : X.width=o.K)
      (i : Bond f) (z : Air f G) : mosaics H p (letter i) F X z = model p R X i := by
    rw [enrolled H p X i z,model]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hread c f S T R μ C H F X i hS hx hk n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))]
  refine ⟨w,hs,?_,?_⟩
  · intro i E _ _ _ F X V u z x Z hx hk hm hχ hV hU
    have hj' := hj (.inr (.inl i)) E F X V u z x Z hx hk hm hχ hV hU
    apply hj'.shimmy
    filter_upwards with y
    change _ - model p R (vary X (V y)) i =
      _ - mosaics H p (letter i) F (vary X (V y)) (z y)
    rw [eq F (vary X (V y)) hx hk]
    rfl
  · intro F X hx hk hm hχ z i hclear
    have due := hw F X hx hk hm hχ z (.inr (.inl i)) hclear
    exact ⟨due.1, (eq F X hx hk i z) ▸ due.2⟩

end YM.Integration.WilsonGaussianDeterminantRoster
end
