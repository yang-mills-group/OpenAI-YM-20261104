import YangMills.LatticeSections
import YangMills.Existence
import YangMills.WilsonProof.TreeUniform
import Solution.OPECoefficients
import MaxwellBridge
import WardBridge
import TraceBridge
import YM.Independent.Core
import YM.Independent.ConstructionRun
import Solution.PhaseReconstruction
import Solution.PhaseObservable
import Solution.AllRadiiBridge
import Solution.PointReturns
import Solution.Research.IssuedRuns.CutoffTrajectory
import Solution.Research.IssuedBridge.FieldQuotient

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable section
open Filter
open scoped Topology

open YangMills YangMills.Wilson YM.Spec YM.OPE.Orbits YM.Nonperturbative

theorem YangMills.jointExistence (g : YangMills.GaugeGroup) (simple : g.IsSimple) :
    ∃ (free : YangMills.Maxwell.Reference g) (run : YangMills.Wilson.Construction g),
      run.Realizes free := by
  let nativeSimple := GaugeGroup.coreSimple simple
  have one : (0 : ℝ) < 1 := by norm_num
  let R := YM.Independent.fundedRun nativeSimple one
  obtain ⟨_, W, _, funded, _⟩ := (YM.Independent.constructionRun nativeSimple one).choose_spec
  have broad := YM.R2IGoals.fromFunded.{0} W nativeSimple funded
  obtain ⟨points, fixed, outer⟩ := LeanPointReturns.nativeReturns R nativeSimple broad.jewel.fullMesh
  let B := maxwellReference g
  let D := IssuedRuns.FinalWilsonData.latticeData R.family R.makes simple B
  have each (request : YM.Extraction.Sequence) :
      ∃ V : VolumeChoice (wilsonFamily R.family),
        ContinuumLimit D points (request.choose ∘ V.indices) V.hierarchy := by
    let order : YM.Extraction.Order := ⟨.full, request⟩
    obtain ⟨q, _, S, F, X, L, Q, _, ordered, _, first, reconstructed, trace, services,
      foundation, trees, _⟩ := broad.refine order
    have core := YM.Independent.Core.of_receipts.{0,0} nativeSimple F L Q reconstructed trace
      services.toServices foundation
    have ope : Headline.SeparatedOPE F Q := by
      refine ⟨core.ope.coefficients, ?_, core.joint⟩
      intro I J _ _ d e a b M η c ε hM hη hc hε degree
      exact core.point a b hM hη hc hε degree
    have tr : Headline.TraceExclusions.{0,0} F :=
      ⟨core.trace.centered, core.trace.identified, core.trace.shortDistance,
       core.trace.positive, core.trace.wick,
       fun n U physical unit translations => core.trace.maxwell n U ⟨physical, unit, translations⟩,
       core.trace.invariant⟩
    have sampled := FixedFields.sampledEstimates F Q X first nativeSimple foundation trace core.services
    obtain ⟨frame, comparison, bounds⟩ := AllRadii.extendFrame F Q X first nativeSimple foundation trace sampled
    refine ⟨⟨q.per.choose, q.per.monotone, hierarchy F Q⟩, {
      smeared := wilsonLimit F Q (s := (order.refine q).per) ordered
      pointwise := outer F Q
      reconstruction := publicReconstruction F Q L reconstructed
      fieldSpace := IssuedExistencePhase.FieldTable.tables F Q
      vacuumSectors := ⟨IssuedExistencePhase.VacuumReconstruction.phases F Q L reconstructed⟩
      adjoints := IssuedBridge.FieldQuotient.adjoints R.makes simple B F Q
      phaseCorrelations := IssuedBridge.PhaseCorrelations.law F Q D rfl
      ope := publicOPE F Q ope
      coefficients := publicCoefficientLaws F Q
      fusionTrees := YM.Integration.WilsonSharpPhysicalTreeGeometry.onFiledUniform F Q trees
      ward := ⟨publicWards F Q⟩
      trace := publicTrace F Q simple tr
      ultraviolet := AllRadii.maxwellLimit B (hierarchy F Q) (publicScaling F Q X first) frame sampled comparison bounds }⟩
  let select (p : ℕ → ℕ) (hp : StrictMono p) := (each ⟨p, hp⟩).choose
  refine ⟨B, ⟨wilsonFamily R.family, select⟩, ?_⟩
  exact ⟨IssuedRuns.CutoffTrajectory.realizes R.family R.makes simple B,
    D, points, fixed, fun p hp => (each ⟨p, hp⟩).choose_spec⟩

end
