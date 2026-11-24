import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalCharacterSlots
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.OriginalPhaseSeparation
open YangMills YangMills.Wilson YM YM.Spec YM.OPE.Orbits
open Function Set
open scoped Topology NNReal
variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

theorem original : Function.Injective (ObservablePhases.signature (hierarchy F Q)) := by
  intro i j measured
  let P := F.α.unselected
  let A := P.algebra
  let left := F.α.space.character i
  let right := F.α.space.character j
  let E := StarAlgHom.equalizer left right
  let M := E.map A.subtype
  have ec : IsClosed (E : Set A) :=
    isClosed_eq (F.phase.phase.decomposition.values i) (F.phase.phase.decomposition.values j)
  have ac : IsClosed (A : Set F.α.room.VacuumOp) := StarSubalgebra.isClosed_topologicalClosure (StarAlgebra.adjoin ℂ P.generators)
  have mc : IsClosed (M : Set F.α.room.VacuumOp) := by
    rw [show (M : Set F.α.room.VacuumOp) = A.subtype '' (E : Set A) from StarSubalgebra.coe_map _ _]
    exact ac.isClosedMap_subtype_val _ ec
  have gen : StarAlgebra.adjoin ℂ P.generators ≤ M := by
    apply StarAlgebra.adjoin_le
    rintro x ⟨w,d,hs,rfl⟩
    exact StarSubalgebra.mem_map.mpr ⟨P.slot w d hs,OriginalCharacterSlots.detected F Q i j measured w d hs,rfl⟩
  have cover : A ≤ M := StarSubalgebra.topologicalClosure_minimal gen mc
  apply F.phase.phase.decomposition.onto.1
  ext x
  obtain ⟨u,hu,equ⟩ := StarSubalgebra.mem_map.mp (cover x.property)
  have identical : u = x := Subtype.ext equ
  exact identical ▸ (show left u = right u from hu)

end IssuedBridge.OriginalPhaseSeparation
end
