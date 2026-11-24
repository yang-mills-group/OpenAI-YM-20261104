import YM.Integration.WilsonCenteredNestedPairTicket

/-! Exact finite address reindexing of the true parent, both incoming
children and the separate far field on the original raw five-node tree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedTicketSites
open Function Finset Spec Extraction Table OPE OPE.Orbits OPE.Prescription OPE.Arboreal
open WilsonThermometerWeakPairFork WilsonCenteredNestedPairTicket
open scoped Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def pair {V:Type} (x:Fin 5→V) (i j:Fin 5) : Fin 2→V := ![x i,x j]
def trio {V:Type} (x:Fin 5→V) : Fin 3→V := ![x 2,x 3,x 4]
def nodes {V:Type} (v:Fin 3→V) : Fin 5→V := ![v 0,v 0,v 0,v 1,v 2]

private def eqv (i j : Fin 5) (ne : i≠j) : Fin 2 ≃ ({i,j} : Finset (Fin 5)) where
  toFun := Fin.cons ⟨i, by simp⟩ (fun _:Fin 1=>⟨j,by simp⟩)
  invFun x := if x.val=i then 0 else 1
  left_inv n := by fin_cases n <;> simp [Ne.symm ne]
  right_inv x := by
    apply Subtype.ext
    rcases (by simpa only [mem_insert,mem_singleton] using x.property : x.val=i∨x.val=j) with h|h
    · simp [h]
    · simp [h,Ne.symm ne]

private lemma pairSites {V:Type} (x:Fin 5→V) (i j:Fin 5) (h:i≠j) :
    crop x {i,j} ∘ eqv i j h = pair x i j := by funext l;fin_cases l <;> rfl

private def terminals : Fin 3 ≃ frame.leaves where
  toFun i := ⟨⟨2+i.val,by omega⟩,by rw [leave];fin_cases i <;> decide⟩
  invFun x := ⟨(x.val:ℕ)-2, by have := x.val.isLt;omega⟩
  left_inv i := by apply Fin.ext;dsimp;omega
  right_inv x := by
    apply Subtype.ext
    apply Fin.ext
    have he : (x.val:Fin 5)∈({2,3,4}:Finset (Fin 5)) := (show frame.leaves ⊆ {2,3,4} from leave.le) x.property
    have hc : 2≤(x.val:ℕ) := by
      rcases (by simpa only [mem_insert,mem_singleton] using he : x.val=2∨x.val=3∨x.val=4) with h|h|h <;> rw [h] <;> decide
    dsimp
    omega

private lemma terminalSites {V:Type} (x:Fin 5→V) :
    crop x frame.leaves ∘ terminals = trio x := by funext l;fin_cases l <;> rfl

theorem whole_row (p:Fin 5→C.book.Token) (w:Mode F.sector.derivatives) (X:Fin 5→E4) :
    whole F Q p w X = Q.port.ope w (trio X) (trio p) (X 0) := by
  symm
  rw [←terminalSites X,←terminalSites p]
  exact Prescription.coefficient_perm Q.port _ Q.continuum.laws.toSymmetric terminals w

lemma inner (p:Fin 5→C.book.Token) (w:Mode F.sector.derivatives) (X:Fin 5→E4) :
    coalesce Q.port WilsonThermometerWeakPairRooms.near X p 1 w =
      Q.port.ope w (pair X 2 3) (pair p 2 3) (X 1) := by
  symm
  rw [←pairSites X 2 3 (by decide),←pairSites p 2 3 (by decide)]
  exact Prescription.coefficient_perm Q.port _ Q.continuum.laws.toSymmetric _ w

lemma outer (p:Fin 5→C.book.Token) (w:Mode F.sector.derivatives) (X:Fin 5→E4) :
    coalesce Q.port WilsonThermometerWeakPairRooms.outside X p frame.root w =
      Q.port.ope w (pair X 1 4) (pair p 1 4) (X 0) := by
  symm
  rw [←pairSites X 1 4 (by decide),←pairSites p 1 4 (by decide)]
  exact Prescription.coefficient_perm Q.port _ Q.continuum.laws.toSymmetric _ w

theorem tree_row (p:Fin 5→C.book.Token) (w:Mode F.sector.derivatives) (D:ℕ) (X:Fin 5→E4) :
    tree F Q p w D X = ∑j∈bands F.sector.derivatives D,
      Q.port.ope j (pair X 2 3) (pair p 2 3) (X 1) *
        Q.port.ope w (pair X 1 4) ![Q.port.letter j,p 4] (X 0) := by
  unfold tree
  apply Finset.sum_congr rfl
  intro j _
  rw [inner F Q,outer F Q]
  apply congrArg (fun v=>Q.port.ope j (pair X 2 3) (pair p 2 3) (X 1)*Q.port.ope w (pair X 1 4) v (X 0))
  funext i
  fin_cases i <;> simp [pair]

end YM.Integration.WilsonCenteredNestedTicketSites
