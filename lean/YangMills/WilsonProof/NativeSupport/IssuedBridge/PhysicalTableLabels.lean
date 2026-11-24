import YangMills.WilsonProof.NativeSupport.WilsonReconstruction
import YangMills.WilsonProof.NativeSupport.HierarchyBridge
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedBridge.PhysicalTableLabels
open YM YangMills Function Set
open YM.Spec YM.OPE YM.OPE.Orbits YM.Nonperturbative YM.Boundary
variable {g : GaugeGroup} {C : YM.Family g.core} {o : YM.Extraction.Order} {S : YM.Table C.book}
variable (F : Final C o S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {n : ℕ} {x : YM.Points n}

theorem filtration : Monotone (fun d => LinearMap.range ((hierarchy F Q).toLabel d)) := by
  rintro d e h _ ⟨v,rfl⟩
  exact ⟨_, F.sector.derivatives.stays F.room.kernel.laws.toSymmetric (spectate_ready F none) h v⟩

theorem unitInGrade (d : ℕ) :
    (hierarchy F Q).toLabel 4 (hierarchy F Q).unitAtFour ∈ LinearMap.range ((hierarchy F Q).toLabel d) :=
  ⟨S.unit d, F.sector.derivatives.unit_same F.room.kernel.laws.toSymmetric (spectate_ready F none) F.room.kernel.laws⟩

theorem empty (s : Option (hierarchy F Q).Character) (v : Fin 0 → (hierarchy F Q).Tag)
    (x : YangMills.Points 0) : (hierarchy F Q).correlation s v x = 1 := by
  let w : Fin 0 → C.book.Token := Fin.elim0
  have h : S.classTokens ∘ w = v := funext (fun i => Fin.elim0 i)
  have hx : x ∈ conf 0 := fun k => Fin.elim0 k
  change S.useAt (spectator F s) x v = 1
  rw [← h,S.at_project (spectator F s) (spectate F s).laws.toSymmetric (spectate_respects F s) hx]
  exact (spectate F s).laws.trivial w x

theorem sameSlot (s : Viewers F) (hx : x ∈ conf n) (w : Fin n → S.Tag)
    (i : Fin n) (a b : S.Tag) (same : S.pin a.1 a.2 = S.pin b.1 b.2) :
    S.useAt (spectator F s) x (update w i a) = S.useAt (spectator F s) x (update w i b) := by
  rcases a with ⟨d,a⟩
  rcases b with ⟨e,b⟩
  let P := F.sector.derivatives
  have common : P.rise (le_max_left d e) a = P.rise (le_max_right d e) b := by
    apply S.pin_inj (max d e)
    rw [P.stays F.room.kernel.laws.toSymmetric (spectate_ready F none),
      P.stays F.room.kernel.laws.toSymmetric (spectate_ready F none)]
    exact same
  rw [← P.inclusion_slot (spectate_ready F s) (spectate F s).laws.toSymmetric (le_max_left d e) hx i w a,
    common, P.inclusion_slot (spectate_ready F s) (spectate F s).laws.toSymmetric (le_max_right d e) hx i w b]

theorem sameTuple (s : Viewers F) (hx : x ∈ conf n) (v w : Fin n → S.Tag)
    (same : ∀ i, S.pin (v i).1 (v i).2 = S.pin (w i).1 (w i).2) :
    S.useAt (spectator F s) x v = S.useAt (spectator F s) x w := by
  classical
  let A := fun (a : Finset (Fin n)) (i : Fin n) => if i ∈ a then v i else w i
  have applyAll (a : Finset (Fin n)) : S.useAt (spectator F s) x (A a) = S.useAt (spectator F s) x w := by
    induction a using Finset.induction_on with
    | empty => simp [A]
    | @insert i a hi ih =>
      have hprev : A a = update (A a) i (w i) := by
        funext k
        by_cases h : k = i
        · subst k
          simp [A,hi]
        · simp [update_of_ne h]
      have hnext : A (insert i a) = update (A a) i (v i) := by
        funext k
        by_cases h : k = i
        · subst k
          simp [A]
        · simp [A,h]
      rw [hnext, sameSlot F s hx (A a) i (v i) (w i) (same i), ← hprev]
      exact ih
  rw [← show A Finset.univ = v by simp [A]]
  exact applyAll _

end IssuedBridge.PhysicalTableLabels
end
