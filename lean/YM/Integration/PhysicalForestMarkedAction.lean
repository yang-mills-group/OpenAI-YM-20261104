import YM.Integration.PhysicalForestAction

/-! Relative and absolute original forest charts carry the entire inherited marked roster and original vacuum together. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalForestMarkedAction

open Function Filter Lattice Wilson RG Precision Exterior Tree
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Power.Roam FreeResolvent Comparison.RG02
open MeasureTheory Stationary Marker Multi Matrix
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio)
variable (M : Matrix (Woods G f) (Woods G c) ℝ)
variable (ρ : fieldDir G c 1 → AxisChart G F)
variable {p : Clip} {P : PathData G} {O : ChartRatio G}
variable {V : Type} [DecidableEq V] {C : Census V}


open PhysicalForestAction

/-- Actual common-chart integrands at fixed tag, including the full positive-degree old exponent, Jacobian,
and every independently installed occupied group function evaluated on the identical original field. -/
theorem complete (K : Bulk.Kernel S p P O) (t : S.Choices) (W : Bulk.Colors C G f)
    (hM : M = reveal G S F * ((reveal G S F).transpose * M))
    (h : ContDiffAt ℝ ω ρ 0) (h₀ : ρ 0=0) :
    ∀ᶠ w : Sloc S F G in 𝓝 0, ∀ g : ℝ,
      let z := Cameo.spider (shore S F M ρ) w
      Bulk.geometric K F t W (g,physical S F ρ w) =
        absoluteAction S F M (p:=p) (P:=P) (O:=O) W g z -
          g^2 * Real.log (edgeM (shore S F M ρ) w).det ∧
      ∀ J : Multi.Hot C, Bulk.markFn S F W J (g,physical S F ρ w) =
        W.mark J g (field S F M z) := by
  filter_upwards [action_germ S F M ρ K t W hM h h₀, tilted S F M ρ hM h h₀] with w action groups
  intro g z
  refine ⟨action g, ?_⟩
  intro J
  exact congrArg (fun U=>W.mark J g U) groups.symm

end YM.Integration.PhysicalForestMarkedAction
