import YM.Integration.PhysicalForestAction
import YM.PertExtension.Uniform

/-! The genuine scaled sample and all its unmarked Taylor coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalForestRay
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

def sample : Sloc S F G := Sum.elim z (flatten x)

theorem exact_sample (g : ℝ) :
    (g, physical S F (fderiv ℝ (K.b F) 0) (g • sample S F x z)) =
      g • Bulk.translated K F x z := by
  rw [Bulk.footing]
  have hb : badge S F (g • sample S F x z) = g • x := by
    change arm G c 1 (g • flatten x) = _
    rw [map_smul]
    rfl
  have ha : (sedan S F (fderiv ℝ (K.b F) 0) (g • sample S F x z)).1 =
      g • (fderiv ℝ (K.b F) 0 x + tape z) := by
    change vcloth S F G (g • z) + (fderiv ℝ (K.b F) 0) (badge S F _) = _
    rw [hb, map_smul, map_smul, smul_add, add_comm]
    rfl
  apply Prod.ext
  · simp
  · exact Prod.ext hb ha

def chartAction (_ : S.Choices) (W : Bulk.Colors C G f) (g : ℝ) : ℝ :=
  let w := g • sample S F x z
  let θ := shore S F M (fderiv ℝ (K.b F) 0)
  absoluteAction S F M (p:=p) (P:=P) (O:=O) W g (Cameo.spider θ w) -
    g^2 * Real.log (edgeM θ w).det

theorem ray (t : S.Choices) (W : Bulk.Colors C G f)
    (hM : M = reveal G S F * ((reveal G S F).transpose * M)) :
    (fun g : ℝ => Bulk.geometric K F t W (g • Bulk.translated K F x z)) =ᶠ[𝓝 0]
      chartAction S F M K x z t W := by
  have h : Tendsto (fun g : ℝ => g • sample S F x z) (𝓝 0) (𝓝 0) := by
    simpa only [zero_smul] using
      (show Continuous (fun g : ℝ => g • sample S F x z) from
        continuous_id.smul continuous_const).tendsto (0 : ℝ)
  filter_upwards [h.eventually (linear_action S F M K t W hM)] with g hg
  rw [← exact_sample S F K x z g]
  exact hg g

theorem coefficient (t : S.Choices) (W : Bulk.Colors C G f) (hW : Bulk.Well W)
    (hM : M = reveal G S F * ((reveal G S F).transpose * M)) (k : ℕ) :
    Assembly.jet (Bulk.geometric K F t W) k (Bulk.translated K F x z) =
      (k.factorial : ℝ)⁻¹ * iteratedDeriv k (chartAction S F M K x z t W) 0 := by
  rw [Assembly.jet_eq]
  rw [PertExtension.Series.Radial.homogeneous_derivative (Bulk.geometric K F t W)
    (Bulk.translated K F x z) k
    ((Bulk.geometric_ready K F t W hW).1.1.of_le (WithTop.coe_le_coe.mpr le_top))]
  apply congrArg (fun y : ℝ => (k.factorial : ℝ)⁻¹ * y)
  exact Filter.EventuallyEq.iteratedDeriv_eq k (ray S F M K x z t W hM)

end YM.Integration.PhysicalForestRay
