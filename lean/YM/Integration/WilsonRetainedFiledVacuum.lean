import YM.Integration.WilsonRetainedMeasuredForestAction
import YM.Integration.WilsonPhysicalHistoryRetainedSpringField

/-! The signed vacuum difference tested by the real short-log estimate.
The independent curvature roster is evaluated at the original fine field. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000

noncomputable section
namespace YM.Integration.WilsonRetainedFiledVacuum
open Function Filter Matrix Lattice Wilson RG RG.Supply Precision Exterior Tree Bloch
open Pressure Pressure.Testing PhysicalNext.Repeat.Legato FreeResolvent
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open Comparison.RG02 Stationary Marker Multi ConnectedActivityE6.Coat
open LocalComparison Global FullQLocal IterationFour IterationFour.Vacuum
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner

variable {G : Gauge} (R : Run G) {N m per r : ℕ} (P : Plan R.family N per r)
variable {V : Type} [DecidableEq V] {C : Census V}
local notation "a" => R.family.path.levels
set_option quotPrecheck false in
local notation "Δ" => (a).clock.op m per
local notation "Y" => R.family.path.rep N per (m+1)
local notation "T" => ships R.alloy.B N m per
variable (hm : m<N) (F : Forest (R.family.path.levels.clock.op m per).ratio)
  (k : (R.family.path.levels.clock.op m per).Choices)
set_option quotPrecheck false in
local notation "K" => (RunFormalChain.fromRun R).step N m per hm
set_option quotPrecheck false in
local notation "M₀" => extractV G (Δ) F (installed (Δ).ratio (R.alloy.B.M.towers N m).A0)

def model (i : ℕ) (W : Bulk.Colors C G (R.family.side i per)) :
    Bulk.Colors C G (R.family.side i per) :=
  {W with vac := ActualAnalyticPlanVacuum.vacuum R P i}

def filed (i : ℕ) (g : ℝ) (U : Config G (R.family.side i per)) : ℝ :=
  let B := ((a).params i).clip
  let Q := (R.family.path.rep N per i).path
  P.alpha i * secondTerm B Q U + ((P.poly i g - P.alpha i)*mainTerm B Q U +
    P.alpha i*OriginalMarkedRunAction.interaction Q U +
    (Integral.temperature g*ActualAnalyticPlanVacuum.radicand R P i g)*
      ((P.layers i).map (fun b=>(ActualAnalyticPlanVacuum.coupling R P i g)^(b.power+2-b.rank)*
        unmaskedPayload b.packet U)).sum)

/-- The exact microscopic operand for the remaining old-action comparison.
All common Gaussian, loop, block and relative area terms have cancelled;
the original old activity and the filed curvature sum use the same field. -/
theorem original (W : Bulk.Colors C G ((a).S.side (m+1) per)) :
    let D := fderiv ℝ ((K).b F) 0
    let θ := shore (Δ) F (M₀) D
    let g := gStep (Y).beta
    ∀ᶠ w : Sloc (Δ) F G in 𝓝 0,
      let h := PhysicalForestAction.physical (Δ) F D w
      let U := Work.F03.live F h
      (Y).beta *
        (g^2*(WilsonRetainedAffineAction.logRead F (M₀) R.metals.O (T) ((a).clock.hatBeta m)
          (Y) (Cameo.spider θ w) - Real.log (edgeM θ w).det) -
          Bulk.geometric (K) F k (model R P (m+1) W) (g,h)) =
        (Y).activities.additive (Y).p U - filed R P (m+1) g U := by
  intro D θ g
  have price := (RunPhysicalMarks.actual_intake R N per m hm).positive
  have hg : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr price)
  have ht : Integral.temperature g = (Y).beta := by
    dsimp [g,Integral.temperature,gStep]
    rw [inv_pow,inv_inv,Real.sq_sqrt price.le]
  have hb : (Y).beta*g^2=1 := by
    rw [←ht]
    exact inv_mul_cancel₀ (pow_ne_zero _ hg.ne')
  filter_upwards [WilsonRetainedMeasuredForestAction.original R N m per hm F k
      (model R P (m+1) W)] with w hi
  dsimp only
  rw [←hi]
  let h := PhysicalForestAction.physical (Δ) F D w
  let U := Work.F03.live F h
  let Z := model R P (m+1) W
  have keep :
      Bulk.geometric (K) F k (WilsonRetainedAffineAction.incoming (Y) Z) (g,h) -
      Bulk.geometric (K) F k Z (g,h) =
        g^2 * (Y).activities.additive (Y).p U - ActualAnalyticPlanVacuum.vacuum R P (m+1) g U := by
    unfold Bulk.geometric Bulk.fee Bulk.supplement Bulk.posed
    dsimp only [WilsonRetainedAffineAction.incoming,Z,model]
    ring
  change (Y).beta * (_-_) = (Y).activities.additive (Y).p U - filed R P (m+1) g U
  rw [keep,mul_sub,←mul_assoc,hb,one_mul]
  apply congrArg (fun x : ℝ => (Y).activities.additive (Y).p U-x)
  have hs := OriginalMarkedRunAction.spring_field R P (m+1) hg.ne' U
  dsimp only at hs
  unfold filed
  dsimp only
  rw [←ht]
  linarith only [hs]

end YM.Integration.WilsonRetainedFiledVacuum
