import YM.Integration.ActualInputGeometryJets
import YM.Integration.ActualJointCoordinateMap

/-! Exact separated-coordinate form of the original finite geometric tensors.
The full main/noise score, loop, chart Haar logarithm and every original
nonlinear layer payload are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualInputGeometryCoordinates
open Function Filter Lattice Wilson RG Precision Exterior Marker Tree
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Comparison.RG02.Assembly
open Push.Uniform
open scoped Topology ContDiff Classical BigOperators

section Generic
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip}
    {P : PathData G} {O : ChartRatio G}
    (K : Bulk.Kernel S p P O) (forest : Forest S.ratio) (t : S.Choices)

def arrayGeometry (_K : Bulk.Kernel S p P O)
    (forest : Forest S.ratio) (t : S.Choices) (layers : List (Piece G f))
    (z : ℝ × Positions (Push.Uniform.Joint forest G)) : ℝ :=
  priced forest t p P z.2 + z.1 ^ 2 *
    (loop P (fine G forest z.2) -
      Real.log (∏ i : forest.Free, O.J ((paint forest G z.2).2 i))) +
    (layers.map (fun a => z.1 ^ (a.power + 2 - a.rank) *
      unmaskedPayload a.packet (fine G forest z.2))).sum

/-- This is a full-function identity for the auxiliary restored-layer geometry,
with the original nonlinear fine chart. No supplied vacuum is replaced here. -/
theorem geometry_value (layers : List (Piece G f))
    (z : ℝ × Positions (Push.Uniform.Joint forest G)) :
    ActualInputGeometryJets.geometry K forest t layers (z.1, paint forest G z.2) =
      arrayGeometry K forest t layers z := rfl

end Generic

variable {G : Gauge} (T : Run G)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} {A : NumericSchedule T.family J}
    {datum : LocalFormal.Datum T.family R}
    (I : AnalyticInput J A datum) {Y : Bulk.Chain T.family.path}

local notation "S" => T.family.path.levels.clock.op datum.level datum.period

/-- Every original finite tensor agrees in the literal coupling-plus-Array
coordinates. This retains the original selected input and kernel; only the
already-proved finite contact is used. -/
theorem input_derivatives (x : TestSpace J.tests) (forest : Forest (S).ratio)
    (t : (S).Choices) (n : ℕ) (hn : n ≤ J.order + 2) :
    iteratedFDeriv ℝ n
      (Bulk.geometric (datum.kernel Y) forest t (I.colors x) ∘
        ActualJointCoordinateMap.lift forest) 0 =
      iteratedFDeriv ℝ n
        (fun z : Positions (ActualJointCoordinateMap.Index (G := G) forest) =>
          arrayGeometry (datum.kernel Y) forest t I.layers
            (z none, ActualJointCoordinateMap.fieldPart forest z)) 0 := by
  have hc := ActualInputGeometryJets.contact T I (Y := Y) x forest t
  have hi : ContDiffAt ℝ ω
      (Bulk.geometric (datum.kernel Y) forest t (I.colors x)) 0 :=
    (Bulk.stone_smooth (datum.kernel Y) forest t).add
      (Bulk.fee_starts (datum.kernel Y) forest (I.colors x)
        (I.whole_input.standard x).1).smooth
  have hg : ContDiffAt ℝ ω
      (ActualInputGeometryJets.geometry (datum.kernel Y) forest t I.layers) 0 := by
    convert hi.sub hc.smooth using 1
    funext z
    simp only [Pi.sub_apply]
    ring
  change iteratedFDeriv ℝ n
    (Bulk.geometric (datum.kernel Y) forest t (I.colors x) ∘
      ActualJointCoordinateMap.lift forest) 0 =
    iteratedFDeriv ℝ n
      (ActualInputGeometryJets.geometry (datum.kernel Y) forest t I.layers ∘
        ActualJointCoordinateMap.lift forest) 0
  ext v
  rw [ActualJointCoordinateMap.derivative forest hi n v,
    ActualJointCoordinateMap.derivative forest hg n v,
    ActualInputGeometryJets.derivatives T I (Y := Y) x forest t n hn]

end YM.Integration.ActualInputGeometryCoordinates
end
