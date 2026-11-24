import YM.Integration.FundedCorrectedPeriod
import YM.WilsonCoeffUV.Kinetic.Bridge
import YM.Integration.PhysicalForestAction

/-! All three incoming terms of the funded nonlinear period action, including
the kinetic path and its unmasked loop. The scalar normalization and angular
forest penalty stay in their native positions on the positive-action side. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedInteractingPeriod
open Function Filter Finset Lattice Wilson RG Precision Tree Bloch Exterior Stationary Marker Multi Matrix
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam FreeResolvent PowerSeries
open Comparison.RG02 WilsonStartup LocalComparison.Global IterationFour.Vacuum
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {σ C : ℝ}

def potential (B : Clip) (P : PathData G) (Z : SeriesA G) (g : ℝ) (U : Config G n) : ℝ :=
  mainTerm B P U + g^2 * Precision.loop P U + FundedPeriodAction.rendered n Z g U

theorem actual (B : Clip) (P : PathData G) (Z : SeriesA G) (hZ : Draw Z σ C)
    (hd : ∀ a∈Z,0<a.grade) (hσ : 0<σ) (p : BudgetPoint) (g : ℝ) (U : Config G n) :
    mainTerm B P U + g^2 * Precision.loop P U +
      ActualGradedVacuum.restored (Z.map (FundedCorrectedPeriod.piece n p σ C)) g U =
    potential B P Z g U := by
  rw [FundedCorrectedPeriod.restored Z hZ hd hσ p g U]
  rfl

private theorem finite_front (B : Clip) (P : PathData G) (n : Side) : shellK 2 (front P B n) := by
  intro i r hr
  simp only [front,Pi.add_apply,(sprig_count _ 2) i r hr,
    (sprig_count _ 0) i r (by omega),add_zero]

private theorem flash_zero (f : TreeVars G n → ℝ) : flash (sprig f 0) = jet f := by
  rw [sprig_flash]
  ext1 i
  simp only [coeff_mk,zero_add]

theorem series (B : Clip) (P : PathData G) {s A L : ℝ} (hP : P.Bounds B s A L)
    (Z : SeriesA G) (hσ : 0<σ) (hZ : Draw Z σ C) (n : Side) :
    X^2 * flash (front P B n + sands Z n) =
      jet (fun w : TreeVars G n => mainTerm B P (mantle w)) +
      X^2 * jet (fun w : TreeVars G n => Precision.loop P (mantle w)) + FundedPeriodAction.formal n Z := by
  have hi : intended (m:=n) B P = fun w => mainTerm B P (mantle w) := by
    funext w
    unfold intended
    rw [Mosaic.mantle_input]
  have hl : turnSeries P.loop (m:=n) = fun w => Precision.loop P (mantle w) := by
    funext w
    unfold turnSeries Precision.loop
    rw [Mosaic.mantle_input]
  rw [flash_add (finite_shell (finite_front B P n)) (finite_shell (sand_span Z n)),mul_add,
    FundedPeriodAction.packets n hσ Z hZ,front,
    flash_add (finite_shell (sprig_count _ 2)) (finite_shell (sprig_count _ 0)),mul_add,
    (rye_top hP n).2,flash_zero,hi,hl]

variable {V : Type} [DecidableEq V] {K : Census V}

def colors (Q : Bulk.Colors K G n) (p : BudgetPoint) (σ C : ℝ) (Z : SeriesA G) : Bulk.Colors K G n :=
  { Q with vac := ActualGradedVacuum.restored (Z.map (FundedCorrectedPeriod.piece n p σ C)) }

theorem marks (Q : Bulk.Colors K G n) (p : BudgetPoint) (σ C : ℝ) (Z : SeriesA G) :
    (colors Q p σ C Z).mark = Q.mark ∧ (colors Q p σ C Z).power = Q.power := ⟨rfl,rfl⟩

variable {c f : Side} (S : StepData c f) (F : Forest S.ratio)
variable (M : Matrix (Woods G f) (Woods G c) ℝ) {O : ChartRatio G}

theorem absolute (B : Clip) (P : PathData G) (Q : Bulk.Colors K G f)
    (Z : SeriesA G) (hZ : Draw Z σ C) (hd : ∀ a∈Z,0<a.grade) (hσ : 0<σ)
    (p : BudgetPoint) (g : ℝ) (w : Sloc S F G) :
    PhysicalForestAction.absoluteAction S F M (p:=B) (P:=P) (O:=O) (colors Q p σ C Z) g w =
      potential B P Z g (PhysicalForestAction.field S F M w) +
        jointPen G S (panSlice G S F M *ᵥ w) - g^2 * unhaar O (camSlice G S F M *ᵥ w) := by
  unfold PhysicalForestAction.absoluteAction colors potential
  change _ + ActualGradedVacuum.restored (Z.map (FundedCorrectedPeriod.piece f p σ C)) g
    (PhysicalForestAction.field S F M w) = _
  rw [FundedCorrectedPeriod.restored Z hZ hd hσ p g (PhysicalForestAction.field S F M w)]
  ring

end YM.Integration.FundedInteractingPeriod
