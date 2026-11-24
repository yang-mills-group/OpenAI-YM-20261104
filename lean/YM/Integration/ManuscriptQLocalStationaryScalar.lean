import YM.Integration.ManuscriptQLocalAffineScalar
import YM.Integration.PhysicalAffineScalarStationary
import YM.Integration.ManuscriptQLocalStationaryGeometry

/-! The original actual-stage uncut scalar residual and its root-fixed
mixed field calculation on any genuine one-block change of tree. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalStationaryScalar
open Function Filter MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Matrix Pressure Pressure.Testing Pressure.Stores Next.SectorChange Next.SectorChange.Rows
open Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent.Affine
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {I : Type} [DecidableEq I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "x" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "Coarse" => Gaussian.Vec (Raw G (R.family.side d.level d.period))
local notation "room" => ManuscriptQLocalStationaryGeometry.larger R d.cutoff d.level d.period d.below
local notation "funds" => ManuscriptQLocalStationaryGeometry.funds R d.cutoff d.level d.period d.below
local notation "beds" => ManuscriptQLocalStationaryGeometry.alongside R d.cutoff d.level d.period d.below
local notation "paths" => R.alloy.B.support.cap d.cutoff (d.level+1) d.below

/-- The complete retained affine residual, on the actual no-hole stage, has
zero linear response in every chosen physical field direction. -/
theorem residual (k : (S).Choices) (b : Coarse) :
    Tendsto (fun t : ℝ => t⁻¹ • PhysicalAffineScalarUncut.sourceResidual T x k d.forest (t • b))
      (𝓝[≠] 0) (𝓝 0) :=
  PhysicalAffineScalarStationary.residual_rate T x k d.forest beds funds room (paths).width (paths).rows
    (ManuscriptQLocalAffineScalar.positive R d k) b

/-- Each root and each genuine tree switch in the original draw has vanishing
fully mixed second-order residual scalar. The law's paired determinant has
its own density and remains in the independently prescribed scalar. -/
theorem one_tree (k : (S).Choices) (q : Site (R.family.side d.level d.period))
    (F' : {t : Forest (S).ratio // FreeResolvent.Affine.changed S d.forest t q})
    (g : ℝ) (o : Site (R.family.side d.level d.period)) (b e : Coarse) :
    let diff := fun v => PhysicalAffineScalarUncut.rootSquare T x k F'.val g o v -
      PhysicalAffineScalarUncut.rootSquare T x k d.forest g o v
    Tendsto (fun t : ℝ => (t^2)⁻¹ * (diff (t • (b+e)) - diff (t • b) - diff (t • e))) (𝓝[≠] 0) (𝓝 0) := by
  let d' : LocalFormal.Datum R.family Γ := {d with forest := F'.val}
  exact PhysicalAffineScalarStationary.one_tree_mixed_square T x k d.forest beds funds room (paths).width (paths).rows
    (ManuscriptQLocalAffineScalar.positive R d k) q F' (ManuscriptQLocalAffineScalar.positive R d' k) g o b e
end YM.Integration.ManuscriptQLocalStationaryScalar
end
