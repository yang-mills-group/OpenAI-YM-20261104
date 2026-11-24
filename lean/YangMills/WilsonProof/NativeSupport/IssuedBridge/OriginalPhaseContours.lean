import YangMills.WilsonProof.NativeSupport.IssuedBridge.ContinuumTableLaws
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedBridge.OriginalPhaseContours
open YM YangMills Function Set Filter MeasureTheory
open YM.Spec YM.OPE YM.OPE.Orbits YM.Nonperturbative YM.Boundary YM.EveryPhase
open scoped Topology BigOperators
variable {g : GaugeGroup} {C : YM.Family g.core} {o : YM.Extraction.Order} {S : YM.Table C.book}
variable (F : Final C o S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable (L : Almanac F) (valid : Completed F L) (i : F.α.space.X)

def actor : Σ H : HilbertSpace, WightmanTheory H (hierarchy F Q).labels :=
  ⟨stateSpace (L.actors i), view (L.actors i)⟩

theorem stress (a b : YM.Axis) :
    (actor F Q L i).2.adjointLabel (Reconstruction.minkowskiStress (hierarchy F Q) a b) =
      Reconstruction.minkowskiStress (hierarchy F Q) a b := by
  change (L.actors i).J (S.pin 4 (Stress.M F.sector.energy a b)) = S.pin 4 (Stress.M F.sector.energy a b)
  rw [(L.cores i).induced, Stress.M_Herm _ F.phase.transport.conserved F.phase.transport.spots F.phase.transport.spin]

theorem traced :
    (actor F Q L i).2.adjointLabel ((hierarchy F Q).toLabel 4 (hierarchy F Q).stressTrace) =
      (hierarchy F Q).toLabel 4 (hierarchy F Q).stressTrace := by
  change (L.actors i).J (S.pin 4 (TraceExtension.stressTrace F.sector.energy)) = S.pin 4 (TraceExtension.stressTrace F.sector.energy)
  rw [(L.cores i).induced]
  congr 1
  rw [Table.adj,LinearMap.comp_apply,show S.conj F.room.kernel.spin 4 (TraceExtension.stressTrace F.sector.energy) =
    TraceExtension.stressTrace F.sector.energy by simp only [TraceExtension.stressTrace,map_sum,F.phase.transport.conserved.real],
    ← F.phase.transport.spots.signed,TraceExtension.stressTrace_turn F.phase.transport.spin]

theorem centered :
    (actor F Q L i).2.adjointLabel ((hierarchy F Q).toLabel 4 (hierarchy F Q).centeredTrace) =
      (hierarchy F Q).toLabel 4 (hierarchy F Q).centeredTrace := by
  change (L.actors i).J (S.pin 4 (TraceExtension.theta (spectator F (some F.α.atPoint)) F.sector.energy)) = S.pin 4 (TraceExtension.theta (spectator F (some F.α.atPoint)) F.sector.energy)
  rw [(L.cores i).induced, TraceExtension.trace_adj F.phase.transport.conserved F.phase.transport.spin F.phase.transport.spots
    (spectate_respects F (some F.α.atPoint)) (spectate F (some F.α.atPoint))]

theorem shiftEq {n : ℕ} (r : ℝ) (height : Fin n → ℝ) (x : YangMills.Points n) :
    Hierarchy.complexShift r height x = YM.Boundary.shift x (r • height) := by
  funext j
  simp [Hierarchy.complexShift,YM.Boundary.shift,Pi.smul_apply,YangMills.time,YM.time]

theorem spaceEq {n : ℕ} (x : YangMills.Points n) : Hierarchy.spatialPoints x = YM.Boundary.trace x := rfl

def source (identity : ∀ t : TestFunction,
    (actor F Q L i).2.fields.field ((hierarchy F Q).toLabel 4 (hierarchy F Q).unitAtFour) t =
    (∫ x,t x) • LinearMap.id (R := ℂ)) :
    Reconstruction.PhaseSource (hierarchy F Q) i (actor F Q L i).1 (actor F Q L i).2 where
  axioms := view_axioms _ (valid.isTheory i)
  faithful := (L.cores i).faithful
  translations _ v := (L.cores i).letters.identity v
  commonAdjoint := L.letters i
  unitOperator := identity
  stressAdjoint := stress F Q L i
  traceAdjoint := traced F Q L i
  centeredAdjoint := centered F Q L i
  wave := (L.contours i).waves.F
  surface := (L.contours i).world.W
  continuous := (L.cards i).fromPhase.heat.together
  holomorphic := (L.cards i).fromPhase.heat.hol
  euclidean n v x hx := by
    have h := (L.cards i).fromPhase.heat.roots n v (Hierarchy.spatialPoints x) (fun j => YangMills.time (x j)) hx
    have e : YM.Boundary.place (Hierarchy.spatialPoints x) (fun j => YangMills.time (x j)) = x := by
      apply PiLp.ext
      intro j
      exact YM.position_eta (x j)
    rw [e] at h
    exact h
  sliceGrowth n v := by
    obtain ⟨Y,ident,_⟩ := (L.cards i).reveals
    have paid := Y.power.1 n v
    rw [ident] at paid
    obtain ⟨m,K,ge,all⟩ := paid
    refine ⟨m,K,ge,?_⟩
    intro height gap pos separated x
    rw [shiftEq,one_smul]
    exact all height gap pos separated x
  integrable n v height order r pos t := by
    have h : (r • height) ∈ YM.Boundary.east n := fun _ _ hit => mul_lt_mul_of_pos_left (order hit) pos
    have actual := (L.cards i).fromPhase.emerges.int n v _ h t
    simp only [shiftEq,spaceEq,YM.Boundary.Waves.restricted] at actual ⊢
    exact actual
  boundary n v height order t := by
    have actual := (L.cards i).fromPhase.emerges.profile n v height order t
    simp only [shiftEq,spaceEq,YM.Boundary.Waves.atSlopes,YM.Boundary.Waves.restricted] at actual ⊢
    exact actual
  tensor n v tests := ⟨YM.Boundary.Joint.materialize n tests,
    fun x => YM.Boundary.Joint.material_at tests x, (publicMoment _ (L.cores i).meets n v tests).symm⟩

end IssuedBridge.OriginalPhaseContours
end
