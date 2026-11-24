import YM.Integration.ActualInputVacuumJets
import YM.Comparison.RG02.Bulk.Fk

/-! The original full input action fixes the finite geometric vertices used by
Fk. Only those vertices are compared with the same restored layer list; no
full-function replacement of the supplied input vacuum is asserted. The
original nonlinear tree chart, path, noise, Haar term and kernel are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualInputGeometryJets
open Function Filter Lattice Wilson RG Precision Exterior Marker Tree
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology ContDiff Classical BigOperators

/-- An auxiliary geometric function using the complete original layer list. -/
def geometry {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip}
    {P : PathData G} {O : ChartRatio G} (K : Bulk.Kernel S p P O)
    (forest : Forest (S).ratio) (t : (S).Choices) (layers : List (Piece G f))
    (z : Bulk.Joint S forest (G := G)) : ℝ :=
  Bulk.stone forest t K z + Bulk.pillar (F := forest) z * Bulk.officer forest K z +
    Bulk.posed S forest (ActualGradedVacuum.restored layers) z

variable {G : Gauge} (T : Run G)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} {A : NumericSchedule T.family J}
    {datum : LocalFormal.Datum T.family R}
    (F : AnalyticInput J A datum) {Y : Bulk.Chain T.family.path}

local notation "S" => T.family.path.levels.clock.op datum.level datum.period

/-- Contact survives the literal nonlinear tree chart by native joint_receipt. -/
theorem contact (x : TestSpace J.tests) (forest : Forest (S).ratio) (t : (S).Choices) :
    GradeAt (2 + J.order + 1)
      (Bulk.geometric (datum.kernel Y) forest t (F.colors x) -
        geometry (datum.kernel Y) forest t F.layers) := by
  let z : ℝ → Config G (T.family.side (datum.level + 1) datum.period) → ℝ :=
    fun g U => (F.colors x).vac g U - ActualGradedVacuum.restored F.layers g U
  have hz : GradeAt (2 + J.order + 1) (Bulk.projected z) :=
    ActualInputVacuumJets.joint_contact T F x
  have hj := Bulk.joint_receipt S forest hz
  convert hj using 1
  funext u
  simp only [geometry, Bulk.geometric, Bulk.fee, Bulk.supplement,
    Bulk.posed, Pi.sub_apply, z]
  ring

/-- Every complete tensor through the original action order plus two agrees. -/
theorem derivatives (x : TestSpace J.tests) (forest : Forest (S).ratio)
    (t : (S).Choices) (n : ℕ) (hn : n ≤ J.order + 2) :
    iteratedFDeriv ℝ n (Bulk.geometric (datum.kernel Y) forest t (F.colors x)) 0 =
      iteratedFDeriv ℝ n (geometry (datum.kernel Y) forest t F.layers) 0 := by
  have hc := contact T F (Y := Y) x forest t
  have hf : ContDiffAt ℝ ω
      (Bulk.geometric (datum.kernel Y) forest t (F.colors x)) 0 :=
    (Bulk.stone_smooth (datum.kernel Y) forest t).add
      (Bulk.fee_starts (datum.kernel Y) forest (F.colors x)
        (F.whole_input.standard x).1).smooth
  have hg : ContDiffAt ℝ ω (geometry (datum.kernel Y) forest t F.layers) 0 := by
    convert hf.sub hc.smooth using 1
    funext u
    simp only [Pi.sub_apply]
    ring
  have hz := hc.vanish n (by omega)
  ext v
  have hv := congrArg (fun M => M v) hz
  simpa only [iteratedFDeriv_sub_apply (hf.of_le le_top) (hg.of_le le_top),
    _root_.sub_apply, _root_.zero_apply, sub_eq_zero] using hv

/-- The actual normalized signed vacuum vertex, with its j+2 shift and all
original Gaussian coordinates, is exactly the same finite polynomial. -/
theorem naked (x : TestSpace J.tests) (forest : Forest (S).ratio)
    (t : (S).Choices) (j : ℕ) (hj : j ≤ J.order)
    (B : fieldDir G (T.family.side datum.level datum.period) 1) :
    Assembly.naked (Bulk.stage (datum.kernel Y) forest B) (Bulk.hinge forest)
      (Bulk.geometric (datum.kernel Y) forest t (F.colors x)) j =
    Assembly.naked (Bulk.stage (datum.kernel Y) forest B) (Bulk.hinge forest)
      (geometry (datum.kernel Y) forest t F.layers) j := by
  unfold Assembly.naked
  rw [derivatives T F (Y := Y) x forest t (j + 2) (by omega)]

end YM.Integration.ActualInputGeometryJets
end
