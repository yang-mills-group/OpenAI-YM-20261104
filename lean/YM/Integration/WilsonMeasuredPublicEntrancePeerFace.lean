import YM.Integration.WilsonMeasuredPublicEntranceLampFamily
import YM.Integration.WilsonMeasuredCompanionFace
import YM.Integration.WilsonOriginalAlternativeFiniteReturn

/-! The complement multiplying a marked forced owner is exactly the product
of the distinct tested ordinary peers in the same face. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntrancePeerFace
open Finset Function RG Wilson Lattice Marker QuadraticLocal
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] {J : Census V}

theorem select (A : Poly J) (v : V) (s : J.Mode) (owner : v∈s.val) :
    ((A*Poly.send (J.fire v) 1).part s)=A.part ⟨s.val.erase v,J.down s.property _ (erase_subset ..)⟩ := by
  classical
  let r : J.Mode := ⟨s.val.erase v,J.down s.property _ (erase_subset ..)⟩
  have one (u : J.Mode) : (∑ t : J.Mode, if Poly.merges u t s then
      A.part u*(Poly.send (J.fire v) (1:ℂ)).part t else 0)=if Poly.merges u (J.fire v) s then A.part u else 0 := by
    rw [sum_eq_single (J.fire v)]
    · simp [Poly.part_send]
    · intro t _ hn
      simp [Poly.part_send,hn]
    · simp
  have only (u : J.Mode) : Poly.merges u (J.fire v) s ↔ u=r := by
    constructor
    · rintro ⟨dj,h⟩
      have clear : v∉u.val := Finset.disjoint_singleton_right.mp dj
      have plus : insert v u.val=s.val := by simpa [Census.fire,Finset.union_comm] using h
      exact Subtype.ext ((Finset.erase_insert clear).symm.trans (congrArg (fun t : Finset V => t.erase v) plus))
    · rintro rfl
      exact ⟨Finset.disjoint_singleton_right.mpr (by simp [r]),
        by simpa [r,Census.fire,Finset.union_comm] using insert_erase owner⟩
  rw [Poly.part_mul]
  simp_rw [one,only]
  simp [r]

theorem original [Fintype V] {T ι : Type} {G : Gauge} {n : Side} {W : Rep G n} {o : V→Site n}
    (E : Lamps T ι G W.p o J) (v : V) (s : J.Mode) (owner : v∈s.val) (x : T) (U : Config G n)
    (value : V→ℂ) (enrolled : E.log x U=∑i,Poly.send (J.fire i) (value i)) :
    WilsonMeasuredCompanionFace.peers E v s x U=∏i∈s.val.erase v,value i := by
  rw [WilsonMeasuredCompanionFace.peers,select _ _ _ owner,enrolled]
  apply Extra.Trajectories.pass_fire

end YM.Integration.WilsonMeasuredPublicEntrancePeerFace
end
