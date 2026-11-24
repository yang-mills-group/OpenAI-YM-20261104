import YM.Integration.WilsonRetainedAffineAction
import YM.Integration.WilsonOriginalSignedSamplerChart
import YM.Integration.RunPhysicalMarks

/-! The retained logarithm in the original measured relative forest, for
the actual affine prediction of the finite Wilson construction. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000

noncomputable section
namespace YM.Integration.WilsonRetainedMeasuredForestAction
open Function Filter Matrix Lattice Wilson RG RG.Supply Precision Exterior Tree Bloch
open Pressure Pressure.Testing PhysicalNext.Repeat.Legato FreeResolvent FreeResolvent.Affine
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open Comparison.RG02 Stationary Marker Multi ConnectedActivityE6 ConnectedActivityE6.Coat
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner

variable {G : Gauge} (R : Run G) (N m per : ℕ) (hm : m<N)
variable {V : Type} [DecidableEq V] {C : Census V}
local notation "a" => R.family.path.levels
set_option quotPrecheck false in
local notation "Δ" => (a).clock.op m per
local notation "Y" => R.family.path.rep N per (m+1)
local notation "T" => ships R.alloy.B N m per
set_option quotPrecheck false in
local notation "K" => (RunFormalChain.fromRun R).step N m per hm
variable (F : Forest (R.family.path.levels.clock.op m per).ratio)
  (k : (R.family.path.levels.clock.op m per).Choices)
set_option quotPrecheck false in
local notation "M₀" => extractV G (Δ) F (installed (Δ).ratio (R.alloy.B.M.towers N m).A0)
set_option quotPrecheck false in
local notation "M₁" => extractV G (Δ) F (installed (Δ).ratio (predictionA (a) N m))

include hm k in
private theorem frame : (M₀) = reveal G (Δ) F * ((reveal G (Δ) F).transpose * (M₀)) := by
  have same : (M₀) = (M₁) := OriginalMarkedHeatCovariance.affineMatrix R N m per hm F k
  rw [same]
  apply sweeps G (Δ) F (installed (Δ).ratio (predictionA (a) N m)) (freeForms (a) N m)
    (A:=freeForms (a) N (m+1))
  · have pos := (K).hessian_pos F k
    rw [OriginalMarkedHeatCovariance.precision R N m per hm F k] at pos
    exact isUnit_iff_ne_zero.mpr pos.det_pos.ne'
  · exact horizon_step (a) m N hm _ _ (Δ).sizes

/-- Every original tag and forest sees the retained physical logarithm
through the same measured shift, including the free-variable determinant
and the whole old regular activity. -/
theorem original (W : Bulk.Colors C G ((a).S.side (m+1) per)) :
    let D := fderiv ℝ ((K).b F) 0
    let g := gStep (Y).beta
    let θ := shore (Δ) F (M₀) D
    ∀ᶠ w : Sloc (Δ) F G in 𝓝 0,
      Bulk.geometric (K) F k (WilsonRetainedAffineAction.incoming (Y) W)
        (g,PhysicalForestAction.physical (Δ) F D w) =
      g^2 * (WilsonRetainedAffineAction.logRead F (M₀) R.metals.O (T) ((a).clock.hatBeta m)
        (Y) (Cameo.spider θ w) - Real.log (edgeM θ w).det) := by
  intro D g θ
  have input := RunPhysicalMarks.actual_intake R N per m hm
  have hs := zero_lt_one.trans ((a).fits.delayed m)
  have hg : (Y).beta*g^2=1 := by
    dsimp [g,gStep]
    rw [inv_pow,Real.sq_sqrt input.positive.le,mul_inv_cancel₀ input.positive.ne']
  have hθ : Green θ := shore_green (Δ) F (M₀) D D.contDiff.contDiffAt (map_zero D)
  have hzero : θ 0=0 := shore_zero (Δ) F (M₀) D (map_zero D)
  have hc := (Cameo.spider_green hθ).continuousAt.tendsto
  rw [Cameo.spider_zero hzero] at hc
  have abs := WilsonRetainedAffineAction.absolute F (M₀) R.metals.O input hs W
  have rel := PhysicalForestAction.linear_action (Δ) F (M₀) (K) k
    (WilsonRetainedAffineAction.incoming (Y) W) (frame R N m per hm F k)
  filter_upwards [hc.eventually abs,rel] with w hw hr
  calc
    _ = PhysicalForestAction.absoluteAction (Δ) F (M₀) (p:=(Y).clip) (P:=(Y).path)
          (O:=R.metals.O) (WilsonRetainedAffineAction.incoming (Y) W) g (Cameo.spider θ w)
          - g^2 * Real.log (edgeM θ w).det := hr g
    _ = _ := by rw [hw g hg]; ring

end YM.Integration.WilsonRetainedMeasuredForestAction
