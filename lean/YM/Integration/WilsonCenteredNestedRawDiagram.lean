import YM.Integration.WilsonCenteredNestedRawHole

/-! Every terminal raw coefficient of the whole physical parent and
of its genuinely formed child field is the corresponding original
five-node ticket entry, including every intermediate grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedRawDiagram
open Function Filter Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Nesting OPE.Nesting.Atom WilsonCenteredNestedDepositedField WilsonCenteredNestedTicketSites
open WilsonCenteredNestedPairTicket
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def head (v:Fin 3→S.Tag) : Fin 2→S.Tag := ![v 0,v 1]
def named (v:Fin 3→S.Tag) := nodes (names (voices v))

def child (D:ℕ) (X:Fin 5→E4) (v:Fin 3→S.Tag) :=
  shadowOld Q.port D (pair X 2 3) (X 1) (voices (head v))

def formed (D H:ℕ) (X:Fin 5→E4) (v:Fin 3→S.Tag) :=
  shadowOld Q.port H (pair X 1 4) (X 0) (roster D (v 2) (child F Q D X v))

lemma head_names (v:Fin 3→S.Tag) : pair (named v) 2 3=names (voices (head v)) := by
  funext i
  fin_cases i <;> rfl

lemma roster_names (v:Fin 3→S.Tag) : trio (named v)=names (voices v) := by
  funext i
  fin_cases i <;> rfl

lemma literal (v:Fin 3→S.Tag) (D:ℕ) (X:Fin 5→E4) (w:Mode F.sector.derivatives) :
    tree F Q (named v) w D X =
      Q.port.ope w (pair X 1 4) (names (roster D (v 2) (child F Q D X v))) (X 0) := by
  rw [tree_row,head_names,child]
  exact (WilsonCenteredNestedRawHole.original F Q D w (pair X 2 3) (voices (head v)) (v 2) (pair X 1 4) (X 0)).symm

theorem original (v:Fin 3→S.Tag) (D H:ℕ) (X:Fin 5→E4) :
    shadowOld Q.port H (trio X) (X 0) (voices v)-formed F Q D H X v =
      ∑w∈bands F.sector.derivatives H,
        (whole F Q (named v) w X-tree F Q (named v) w D X) • Q.port.loaded w H := by
  unfold formed shadowOld OPE.shadow
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  rw [whole_row,roster_names,literal,sub_smul]

end YM.Integration.WilsonCenteredNestedRawDiagram
