import YM.Integration.WilsonRunVacuumWickCubature
import YM.Integration.WilsonConditionalTaylorKineticProjection

/-! Center the physical logarithm with its own covariance while preserving
all genuine two-leg coefficients of the uncentered finite action. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredVacuumGerm
open Function Matrix PowerSeries Lattice Wilson RG Precision Tree Exterior
open FormalBulk08 Jets Orb Series Reef Flat Push.Uniform Next.Free Comparison.RG02
open MSbar MSbar.Cacao MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal MSbar.Midpoint
open WilsonMovingPolynomialPull WilsonMovingNormalizedBank
open scoped Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}

theorem gauge (Y : Pap (wire G c)) (u : Positions (Primary c G)) :
    view u (place (WilsonMovingGaussianCoordinates.link G c).symm Y) =
    glimpse (FreeResolvent.flatten (tint G (Body 1 c) u)) Y := by
  exact placed (WilsonMovingGaussianCoordinates.link G c).symm Y u

theorem centered (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)
    (v : Pap (wire G f)) (u : Positions (Primary c G)) :
    view u (colorCut F t P p O (splitV (place (WilsonMovingGaussianCoordinates.link G f).symm v)) (K.b F)) =
      covelog (WilsonRunVacuumWickCubature.bank K F t u v)-covelog (WilsonRunVacuumWickCubature.bank K F t 0 v) := by
  let X := Positions (Primary c G)
  let Y := Positions (Key F G)
  have zero : meetVar (0:X) (0:Y)=0 := (partSpace _ _).symm.map_zero
  have z := ((K.critical F).2.2 t).1
  have moved : ContDiffAt ℝ ω (priced F t p P) (0:Positions (Joint F G)) := by
    unfold priced
    apply ContDiffAt.comp _ _ (paint F G).contDiff.contDiffAt
    rwa [map_zero]
  have bought := Push.Uniform.block_congr F t (zero.symm ▸ moved)
  rw [zero,map_zero,map_zero] at bought
  have pos : (Push.Uniform.block (priced F t p P) 0).PosDef := bought.symm ▸ K.hessian_pos F t
  rw [WilsonConditionalTaylorUntunedLog.one F t P p O _ (K.b F) u pos (splitK _)]
  unfold WilsonConditionalTaylorUntunedLog.filed WilsonRunVacuumWickCubature.bank
  rw [WilsonMovingGaussianGeometry.covariance K F t]

theorem insensitive (v : G.Color) (A B : Pot (Primary c G)) (z : ℝ)
    (same : ∀ u, MvPolynomial.eval u A = MvPolynomial.eval u B + z) :
    caliper c v A=caliper c v B := by
  have identity : A=B+MvPolynomial.C z := by
    apply MvPolynomial.funext
    intro u
    simpa only [map_add,MvPolynomial.eval_C] using same u
  have row : MvPolynomial.homogeneousComponent 2 A=MvPolynomial.homogeneousComponent 2 B := by
    rw [identity,map_add,MvPolynomial.homogeneousComponent_eq_zero 2 (MvPolynomial.C z)
      (show (MvPolynomial.C z : Pot (Primary c G)).totalDegree<2 by simp),add_zero]
  rw [← WilsonConditionalTaylorKineticProjection.two v A,row,WilsonConditionalTaylorKineticProjection.two]

end YM.Integration.WilsonMeasuredVacuumGerm
end
