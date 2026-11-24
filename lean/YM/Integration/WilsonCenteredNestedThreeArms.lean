import YM.Integration.WilsonCenteredNestedRawDiagram
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! The defect of the *two complete trees* is multilinear in all three
incoming fields at their own grades. This permits one fixed ticket
before the common orthogonal or real input branch is chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedThreeArms
open Function Filter Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Nesting OPE.Nesting.Atom WilsonCenteredNestedDepositedField WilsonCenteredNestedTicketSites
open WilsonCenteredNestedRawDiagram WilsonCenteredNestedPairTicket
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def exit (d:ℕ) (w j:Mode F.sector.derivatives) (X:Fin 5→E4) : S.Field d→ₗ[ℂ] ℂ :=
  (checkRow Q.port w (pair X 1 4) (X 0)).toLinearMap (roster j.1 (⟨d,0⟩:S.Tag) (Q.port.needle j)) 1

lemma read_exit (d:ℕ) (w j:Mode F.sector.derivatives) (X:Fin 5→E4) (v:S.Field d) :
    exit F Q d w j X v=Q.port.ope w (pair X 1 4) ![Q.port.letter j,quoteTag (⟨d,v⟩:S.Tag)] (X 0) := by
  have same (dec : DecidableEq (Fin 2)) :
      @update (Fin 2) (fun i=>S.Field (grades j.1 d i)) dec (roster j.1 (⟨d,0⟩:S.Tag) (Q.port.needle j)) 1 v =
        roster j.1 (⟨d,v⟩:S.Tag) (Q.port.needle j) := by
    funext i
    refine Fin.cases ?_ (fun k=>?_) i
    · exact @update_of_ne (Fin 2) (fun i=>S.Field (grades j.1 d i)) dec 0 1 Fin.zero_ne_one v (roster j.1 (⟨d,0⟩:S.Tag) (Q.port.needle j))
    · refine Fin.cases ?_ (fun i=>i.elim0) k
      exact @update_self (Fin 2) (fun i=>S.Field (grades j.1 d i)) dec 1 v (roster j.1 (⟨d,0⟩:S.Tag) (Q.port.needle j))
  have atV : exit F Q d w j X v = Q.port.ope w (pair X 1 4) (names (roster j.1 (⟨d,v⟩:S.Tag) (Q.port.needle j))) (X 0) := (congrArg (checkRow Q.port w (pair X 1 4) (X 0)) (same _)).trans
      (check_eq Q.port _ Q.continuum _ _ _)
  refine atV.trans (congrArg (fun z=>Q.port.ope w (pair X 1 4) z (X 0)) ?_)
  funext i;fin_cases i <;> rfl

def row (d:Fin 3→ℕ) (D:ℕ) (w:Mode F.sector.derivatives) (X:Fin 5→E4) :
    MultilinearMap ℂ (fun i=>S.Field (d i)) ℂ :=
  checkRow Q.port w (trio X) (X 0) -
    ∑j∈bands F.sector.derivatives D,
      ((checkRow (d:=fun i:Fin 2=>d i.castSucc) Q.port j (pair X 2 3) (X 1)).smulRight
        (exit F Q (d (Fin.last 2)) w j X)).uncurryRight

theorem original (d:Fin 3→ℕ) (D:ℕ) (w:Mode F.sector.derivatives) (X:Fin 5→E4) (v:Labels S d) :
    row F Q d D w X v=whole F Q (named (tags v)) w X-tree F Q (named (tags v)) w D X := by
  rw [whole_row,roster_names,tree_row]
  unfold row
  simp only [_root_.sub_apply,_root_.sum_apply,check_eq Q.port w Q.continuum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change checkRow Q.port j (pair X 2 3) (X 1) (Fin.init v) * exit F Q _ w j X (v (Fin.last 2))=_
  rw [check_eq Q.port j Q.continuum,read_exit]
  have two : names (Fin.init v) = pair (named (tags v)) 2 3 := by funext i;fin_cases i <;> rfl
  rw [two]
  rfl

end YM.Integration.WilsonCenteredNestedThreeArms
