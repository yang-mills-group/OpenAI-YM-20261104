import YM.Integration.ActualRunGeometryTensorPrice

/-! The actual selected input's full geometric tensor inherits the original
layer estimate only through the proved finite contact. No equality of the
supplied vacuum away from those derivatives is asserted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualInputVertexPrice
open Function Filter Lattice Wilson RG Precision Tree Exterior Marker
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Push.Uniform Comparison.RG02
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical ContDiff

/-- The original coupling and nonlinear-chart field coordinates, unchanged. -/
def frame {G : Gauge} {c f : Side} {S : StepData c f} (B : Forest S.ratio) :
    (ℝ × Positions (Push.Uniform.Joint B G)) →L[ℝ] Bulk.Joint S B (G := G) :=
  (ContinuousLinearMap.fst ℝ ℝ _).prod
    ((paint B G).toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ ℝ _))

private theorem framed_derivative {G : Gauge} (T : Run G)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} {A : NumericSchedule T.family J}
    {datum : LocalFormal.Datum T.family R}
    (I : AnalyticInput J A datum) {Y : Bulk.Chain T.family.path}
    (x : TestSpace J.tests)
    (B : Forest (T.family.path.levels.clock.op datum.level datum.period).ratio)
    (t : (T.family.path.levels.clock.op datum.level datum.period).Choices)
    (n : ℕ) (hn : n ≤ J.order + 2)
    (v : Fin n → ℝ × Positions (Push.Uniform.Joint B G)) :
    iteratedFDeriv ℝ n (Bulk.geometric (datum.kernel Y) B t (I.colors x)) 0
        (fun j => frame B (v j)) =
      iteratedFDeriv ℝ n
        (ActualInputGeometryCoordinates.arrayGeometry (datum.kernel Y) B t I.layers) 0 v := by
  have hc := ActualInputGeometryJets.contact T I (Y := Y) x B t
  have hi : ContDiffAt ℝ ω (Bulk.geometric (datum.kernel Y) B t (I.colors x)) 0 :=
    (Bulk.stone_smooth (datum.kernel Y) B t).add
      (Bulk.fee_starts (datum.kernel Y) B (I.colors x) (I.whole_input.standard x).1).smooth
  have hg : ContDiffAt ℝ ω
      (ActualInputGeometryJets.geometry (datum.kernel Y) B t I.layers) 0 := by
    convert hi.sub hc.smooth using 1
    funext z
    simp only [Pi.sub_apply]
    ring
  rw [ActualInputGeometryJets.derivatives T I (Y := Y) x B t n hn]
  have he := Push.Loops.Paths.iterated_affine (frame B) 0 0
    (show ContDiffAt ℝ ω
      (ActualInputGeometryJets.geometry (datum.kernel Y) B t I.layers)
      (0 + frame B 0) by simpa only [map_zero, zero_add] using hg) v
  have hframe : (fun z => ActualInputGeometryJets.geometry (datum.kernel Y) B t I.layers
      (frame B z)) = ActualInputGeometryCoordinates.arrayGeometry (datum.kernel Y) B t I.layers :=
    funext (ActualInputGeometryCoordinates.geometry_value (datum.kernel Y) B t I.layers)
  have he' : iteratedFDeriv ℝ n
      (ActualInputGeometryCoordinates.arrayGeometry (datum.kernel Y) B t I.layers) 0 v =
      iteratedFDeriv ℝ n
        (ActualInputGeometryJets.geometry (datum.kernel Y) B t I.layers) 0
        (fun j => frame B (v j)) := by
    simpa only [map_zero, zero_add, hframe] using he
  exact he'.symm

/-- Fixed constants precede every datum, input, kernel, test and coordinate.
The entire original geometric tensor is bounded through the required order. -/
theorem vertices {G : Gauge} (T : Run G) (hG : G.Simple)
    (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (A : NumericSchedule T.family J) :
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℕ,
      ∀ᶠ i : ℕ in atTop,
        ∀ (datum : LocalFormal.Datum T.family R), datum.level = i →
        ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
          (x : TestSpace J.tests)
          (B : Forest (T.family.path.levels.clock.op datum.level datum.period).ratio)
          (t : (T.family.path.levels.clock.op datum.level datum.period).Choices),
        ∀ k : ℕ, k + 1 ≤ J.order + 2 → ∀ j : Fin (k + 1),
          ∀ i0 : Push.Uniform.Joint B G,
          (∑ q : Fin k → Option (Push.Uniform.Joint B G),
            ‖(((k + 1).factorial : ℝ)⁻¹) *
              iteratedFDeriv ℝ (k + 1)
                (Bulk.geometric (datum.kernel Y) B t (I.colors x)) 0
                (fun u => frame B (FiniteOptionSlotMarginal.direction
                  (fun z : Push.Uniform.Joint B G => bolt z)
                  (Fin.insertNth (α := fun _ => Option (Push.Uniform.Joint B G)) j (some i0) q u)))‖) ≤
            C * (A.admittedCost i) ^ e := by
  obtain ⟨C, hC, e, h⟩ := ActualRunGeometryTensorPrice.geometry_marginal
    T hG hT A (J.order + 2) J.vacuumRankCap (by omega)
  refine ⟨C, hC, e, ?_⟩
  filter_upwards [h] with i hi
  intro datum hlevel Y I x B t k hk j i0
  subst i
  have hN : datum.level + 1 ≤ datum.cutoff := by have := datum.below; omega
  have hp := hi datum.cutoff datum.period hN Y.O (datum.kernel Y)
    (A.inputNorm datum.level) J.order I.layers I.vacuum B t k hk j i0
  calc
    _ = ∑ q : Fin k → Option (Push.Uniform.Joint B G),
        ‖(((k + 1).factorial : ℝ)⁻¹) * iteratedFDeriv ℝ (k + 1)
          (ActualInputGeometryCoordinates.arrayGeometry (datum.kernel Y) B t I.layers) 0
          (fun u => FiniteOptionSlotMarginal.direction
            (fun z : Push.Uniform.Joint B G => bolt z)
            (Fin.insertNth (α := fun _ => Option (Push.Uniform.Joint B G)) j (some i0) q u))‖ := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [framed_derivative T I (Y := Y) x B t (k + 1) hk]
    _ ≤ _ := hp

end YM.Integration.ActualInputVertexPrice
end
