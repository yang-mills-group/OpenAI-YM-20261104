import YM.Integration.PhysicalForestRay
import YM.Integration.PhysicalForestMarkedAction

/-! Actual signed marked radial coefficients, keeping the incoming Wilson forest in both coordinate systems. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalForestMarkedRay
open Function Filter Lattice Wilson RG Precision Exterior Tree Matrix
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open FreeResolvent Comparison.RG02 MeasureTheory Stationary Marker Multi Next.SectorChange
open PhysicalForestAction
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio)
variable {p : Clip} {P : PathData G} {O : ChartRatio G}
variable {V : Type} [DecidableEq V] {C : Census V}
variable (M : Matrix (Woods G f) (Woods G c) ℝ) (K : Bulk.Kernel S p P O)
variable (x : fieldDir G c 1) (z : Precision.Key F G → ℝ)


open PhysicalForestRay

def chartMark (W : Bulk.Colors C G f) (J : Hot C) (g : ℝ) : ℂ :=
  let z₀ := g • sample S F x z
  let θ := shore S F M (fderiv ℝ (K.b F) 0)
  W.mark J g (field S F M (Cameo.spider θ z₀))

theorem marked (t : S.Choices) (W : Bulk.Colors C G f) (J : Hot C)
    (hM : M = reveal G S F * ((reveal G S F).transpose * M)) :
    (fun g : ℝ => Bulk.markFn S F W J (g • Bulk.translated K F x z)) =ᶠ[𝓝 0]
      chartMark S F M K x z W J := by
  let D := fderiv ℝ (K.b F) 0
  have moving : Continuous (fun g : ℝ=> g • sample S F x z) := continuous_id.smul continuous_const
  have h : Tendsto (fun g : ℝ => g • sample S F x z) (𝓝 0) (𝓝 0) := by simpa using moving.tendsto (0:ℝ)
  filter_upwards [h.eventually (PhysicalForestMarkedAction.complete S F M D K t W hM D.contDiff.contDiffAt (map_zero D))] with g hg
  rw [← exact_sample S F K x z g]
  exact (hg g).2 J

/-- Both real components are differentiated before integration against the true common Gaussian. -/
def readJet (k : ℕ) (a : ℝ→ℂ) : ℂ :=
  (↑((k.factorial:ℝ)⁻¹ * iteratedDeriv k (Complex.re ∘ a) 0):ℂ) +
    Complex.I * ↑((k.factorial:ℝ)⁻¹ * iteratedDeriv k (Complex.im ∘ a) 0)

theorem coefficient (t : S.Choices) (W : Bulk.Colors C G f) (hW : Bulk.Well W) (J : Hot C)
    (hM : M = reveal G S F * ((reveal G S F).transpose * M)) (k : ℕ) :
    Assembly.jet (Bulk.markFn S F W J) k (Bulk.translated K F x z) =
      readJet k (chartMark S F M K x z W J) := by
  let u := Bulk.translated K F x z
  let ink := Bulk.markFn S F W J
  have smooth := ((Bulk.geometric_ready K F t W hW).2 J).1
  have one (L : ℂ→L[ℝ]ℝ) : Assembly.jet (L ∘ ink) k u =
      (k.factorial:ℝ)⁻¹ * iteratedDeriv k (L ∘ chartMark S F M K x z W J) 0 := by
    rw [Assembly.jet_eq]
    rw [PertExtension.Series.Radial.homogeneous_derivative _ _ k
      ((L.contDiff.contDiffAt.comp 0 smooth).of_le (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤)))]
    apply congrArg (fun a : ℝ => (k.factorial:ℝ)⁻¹ * a)
    apply Filter.EventuallyEq.iteratedDeriv_eq k
    exact (marked S F M K x z t W J hM).fun_comp L
  rw [Assembly.jet_real smooth]
  exact congrArg₂ (fun a b : ℝ => (a:ℂ) + Complex.I * b) (one Complex.reCLM) (one Complex.imCLM)

end YM.Integration.PhysicalForestMarkedRay
