import YM.EveryPhase.Extension

/-!
# Working in an arbitrary phase of a single construction

Build this presentation of `Final` when applying results stated only in the selected phase
but *proved for every Final* for this C and extraction & Table. Use the **same** contours and
field representations as the `Almanac`. In particular no new Choice of Hilbert spaces is
needed and the scaled correlation bounds can be stated using precisely its shapes.

Retains the ENTIRE Resolution (not a point mass), keeps unselected theory, couplings,
copies, normalized observables, O action, stress and fields; no new limits.
For transferring results depending on the J or Lorentz label action use `L.letters, L.spins`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact
open Spec Boundary Extraction EveryPhase
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {F : Final C f S} {L : Almanac F}

def focus (H : Completed F L) (i : F.α.space.X) : Final C f S :=
 { F with
   α := ⟨F.α.room, F.α.unselected, F.α.space, F.α.ensemble, i,
     L.chambers i, L.spreads i⟩
   phase := ⟨F.phase.transport,
     ⟨F.phase.phase.lengths, F.phase.phase.still, F.phase.phase.decomposition,
       F.phase.phase.chosen, F.phase.phase.states, F.phase.phase.sym,
       F.phase.phase.retains, F.phase.phase.coordinates, F.phase.phase.calculus,
       F.phase.phase.flux, (L.pantries i).counter, H.euclid i⟩⟩
   A := L.contours i
   action := L.actors i
   realization := ⟨F.realization.allWorld, (L.cards i).fromPhase, H.isTheory i⟩ }

variable (H : Completed F L) (i : F.α.space.X)

@[simp] lemma focus_sector : (focus H i).sector = F.sector := rfl
@[simp] lemma focus_B : (focus H i).B = F.B := rfl
@[simp] lemma focus_A : (focus H i).A = L.contours i := rfl
@[simp] lemma focus_action : (focus H i).action = L.actors i := rfl
@[simp] lemma focus_selected :
    (focus H i).α.ensemble (focus H i).α.atPoint = F.α.ensemble i := rfl

end YM.GapsContact
