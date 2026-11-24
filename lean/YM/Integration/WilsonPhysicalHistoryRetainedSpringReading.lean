import YM.Integration.WilsonPhysicalHistoryRetainedSpringPitch

/-! The complete finite pre-reset interaction on its actual compact group field.
The signed previous kinetic mismatch is retained in the same observable. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice Wilson RG Precision Exterior IterationFour IterationFour.Vacuum PhysicalNext.Repeat.Legato
open LocalComparison Global FullQLocal Comparison.RG02 Comparison.RG02.Assembly
open MeasureTheory Push.SectorMeasure
open scoped BigOperators Classical
variable {G : Gauge} {N per r : ℕ}

def springReading (R : Run G) (P : Plan R.family N per r) (j : ℕ) (g : ℝ)
    (U : Config G (R.family.side j per)) : ℝ :=
  let K:=(R.family.path.rep N per j).path
  let B:=(R.family.path.levels.params j).clip
  let p:=ActualAnalyticPlanVacuum.radicand R P j g
  let c:=ActualAnalyticPlanVacuum.coupling R P j g
  (pitchDifference R P j g+g^2*pitchTail R N j r g)*mainTerm B K U +
    P.alpha j*interaction K U + (Integral.temperature g*p)*
      ((P.layers j).map (fun a=>c^(a.power+2-a.rank)*unmaskedPayload a.packet U)).sum

theorem spring_reading (R : Run G) (simple : G.Simple) (P : Plan R.family N per r)
    {j : ℕ} (hj : j<N) {g : ℝ} (hg : g≠0) (U : Config G (R.family.side j per)) :
    springReading R P j g U=Integral.temperature g*ActualAnalyticPlanVacuum.vacuum R P j g U-
      P.alpha j*secondTerm (R.family.path.levels.params j).clip (R.family.path.rep N per j).path U := by
  rw [spring_field R P j hg U]
  unfold springReading
  rw [actual_pitch R simple P hj]

theorem spring_envelope (R : Run G) (simple : G.Simple) (P : Plan R.family N per r)
    {j : ℕ} (hj : j<N) {g : ℝ} (hg : g≠0)
    {point : BudgetPoint} {cap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers (P.layers j) point r cap width budget) (pos : 0<width) :
    Envelope (springReading R P j g) := by
  let D:=R.family.path.levels.params j
  have h : R.family.path.Conv N per j := R.makes.wilson.represents N per j hj.le
  have paths : (R.family.path.rep N per j).path.Bounds D.clip D.width D.paths
      (R.family.path.levels.clock.loopCap j) := by
    dsimp only [D]
    rw [←h.clip]
    exact h.good.paths
  have sq : Envelope (secondTerm D.clip (R.family.path.rep N per j).path
      (n:=R.family.side j per)) := by
    unfold secondTerm Patch.average
    exact (Envelope.const _).mul (Envelope.sum _ _ fun i=>
      Env.along (AllOrder.Laplace.env_quad paths) (continuous_pull i 0|>.measurable))
  have vac:=ActualAnalyticPlanVacuum.vacuum_envelope R P j H hj.le pos g
  rw [show springReading R P j g=(fun U=>Integral.temperature g*
      ActualAnalyticPlanVacuum.vacuum R P j g U-P.alpha j*
        secondTerm D.clip (R.family.path.rep N per j).path U) from
    funext (spring_reading R simple P hj hg)]
  simp only [sub_eq_add_neg]
  exact ((Envelope.const _).mul vac).add ((Envelope.const _).mul sq).neg

end YM.Integration.OriginalMarkedRunAction
