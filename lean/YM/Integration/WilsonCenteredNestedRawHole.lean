import YM.Integration.WilsonCenteredNestedDepositedField
import YM.Integration.WilsonCenteredNestedTicketSites

/-! Price the exact original raw two-vertex contraction after the entire
inner field is inserted in the outer word.  The intermediate letter in
the genuine LogTrace table is precisely its own original needle. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedRawHole
open Function Filter Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Nesting OPE.Nesting.Atom WilsonCenteredNestedDepositedField
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def hole (D:ℕ) (w:Mode F.sector.derivatives) (far:S.Tag) (y:Fin 2→E4) (o:E4) :
    S.Field D→ₗ[ℂ] ℂ := (checkRow Q.port w y o).toLinearMap (roster D far 0) 0

lemma through (D:ℕ) (w:Mode F.sector.derivatives) (far:S.Tag) (y:Fin 2→E4) (o:E4) (v:S.Field D) :
    hole F Q D w far y o v=Q.port.ope w y (names (roster D far v)) o := by
  have same (dec : DecidableEq (Fin 2)) :
      @update (Fin 2) (fun i=>S.Field (grades D far.1 i)) dec (roster D far 0) 0 v=roster D far v := by
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact @update_self (Fin 2) _ dec 0 v (roster D far 0)
    · exact @update_of_ne (Fin 2) _ dec j.succ 0 (Fin.succ_ne_zero j) v (roster D far 0)
  exact (congrArg (checkRow Q.port w y o) (same _)).trans (check_eq Q.port _ Q.continuum _ _ _)

lemma letter (D:ℕ) (w j:Mode F.sector.derivatives) (hj:j∈bands F.sector.derivatives D)
    (far:S.Tag) (y:Fin 2→E4) (o:E4) :
    hole F Q D w far y o (Q.port.loaded j D) =
      Q.port.ope w y ![Q.port.letter j,quoteTag far] o := by
  rw [through]
  symm
  apply WilsonThermometerWeakPairRise.coefficient Q.port Q.spans Q.continuum.laws.toSymmetric Q.lifts
  intro i
  refine Fin.cases ?_ (fun u=>?_) i
  · refine Or.inr ⟨(full_bands ..).mp hj,?_⟩
    change F.sector.derivatives.rise _ (S.project j.1 (S.representative _ (Q.port.needle j))) =
      S.project D (S.representative D (Q.port.loaded j D))
    erw [S.rep,S.rep,cost Q.port j hj]
  · refine Fin.cases ?_ (fun i=>i.elim0) u
    exact Or.inl rfl

theorem original {I:Type} [Fintype I] {d:I→ℕ} (D:ℕ) (w:Mode F.sector.derivatives)
    (x:I→E4) (v:Labels S d) (far:S.Tag) (y:Fin 2→E4) (o:E4) :
    Q.port.ope w y (names (roster D far (shadowOld Q.port D x (y 0) v))) o =
    ∑j∈bands F.sector.derivatives D,
      Q.port.ope j x (names v) (y 0) * Q.port.ope w y ![Q.port.letter j,quoteTag far] o := by
  rw [←through F Q]
  unfold shadowOld OPE.shadow
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul,letter F Q D w j hj]
  rfl

end YM.Integration.WilsonCenteredNestedRawHole
