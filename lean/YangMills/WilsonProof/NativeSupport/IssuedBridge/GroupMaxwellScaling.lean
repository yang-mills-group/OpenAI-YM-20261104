import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Reference
import YangMills.WilsonProof.NativeSupport.IssuedBridge.AllOriginalPhases
set_option autoImplicit false
noncomputable section
namespace YangMills.IssuedPhysical
open YM YM.Spec YM.OPE.Orbits YM.Maxwell YM.Maxwell.Free
open Function Filter Set
open scoped Topology BigOperators InnerProductSpace Classical

variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def issuedScaling (X : Climb.Scaling S) (h : Pert.FirstExtension F X) :
    (hierarchy F Q).MaxwellScaling (IssuedMaxwell.Reference.issued g) where
  r := X.r
  positive := X.positive
  later := X.later
  drips := X.drips
  frame k d := (fields C.labels d).symm.trans (X.U k d)
  jets n j q marked ab K hK hsep ε hε := by
    let v (i : Fin n) : (freeTable C.labels).Tag := ⟨(q i).1,(fields C.labels _).symm (q i).2⟩
    have hh := h.jets n j v marked ab hK hsep hε
    have free (z : Points n) : Ward.disc (Pert.freeWithStress C.labels v marked ab) z =
        Wick.moment g.core z (fun i => if marked i then -polStress g.core (ab i).1 (ab i).2
          else (q i).2.val) := by
      rw [Ward.disc, display]
      congr 1
      funext i
      change supply C.labels (Pert.freeWithStress C.labels v marked ab i) = _
      unfold Pert.freeWithStress
      split_ifs with hi
      · change address C.labels 4 (-original C.labels (ab i).1 (ab i).2) = _
        rw [map_neg,inertia]
      · exact congrArg Subtype.val ((fields C.labels (q i).1).apply_symm_apply (q i).2)
    rw [funext free] at hh
    exact hh

end YangMills.IssuedPhysical
end
