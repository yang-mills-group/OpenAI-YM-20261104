import YM.Integration.WilsonCenteredNestedPairChord
import YM.Integration.WilsonCenteredNestedTicketSites
import YM.Integration.WilsonCenteredNestedRawDiagram

/-! Route the two inner leaves and the outer leaf of the original plot
through the actual OPE reader. The root and inner anchors stay distinct. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedTreeLeaves
open Function Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Atom
open OPE.Nesting.Tree OPE.Nesting.Composite WilsonCenteredNestedTwoVertex WilsonCenteredNestedPairConvoy
open WilsonCenteredNestedPairChord WilsonCenteredNestedTicketSites WilsonCenteredNestedRawDiagram
open scoped Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def leafList : Fin 3→full.Leaf := ![⟨0,⟨0,()⟩⟩,⟨0,⟨1,()⟩⟩,⟨1,()⟩]

private def index (x:full.Leaf) : ℕ :=
  Fin.cases (motive:=fun i=>(arms i).Leaf→ℕ) (fun j=>j.1.val) (fun _ _=>2) x.1 x.2

private lemma recovery (i:Fin 3) : index (leafList i)=i.val := by fin_cases i <;> rfl

def order : Fin 3 ≃ full.Leaf := Equiv.ofBijective leafList <| by
  constructor
  · intro i j he
    exact Fin.ext ((recovery i).symm.trans ((congr_arg index he).trans (recovery j)))
  · rintro ⟨i,j⟩
    fin_cases i
    · change (Σ _i:Fin 2,Unit) at j
      rcases j with ⟨l,un⟩
      cases un
      fin_cases l
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
    · change Unit at j
      cases j
      exact ⟨2,rfl⟩

abbrev roster (v:full.Leaf→S.Tag) := v ∘leafList

lemma inner (v:full.Leaf→S.Tag) : head (roster v)=near v := by funext i;fin_cases i <;>rfl

theorem original (m:ℕ) (c:Q.channels m) (z:full.Plot) (v:full.Leaf→S.Tag) :
    express Q m c (trio (sites z)) (roster v) (sites z 0)=Kernel.output F Q z v c := by
  apply express_reindex (z:=Tree.profile z) (w:=v) Q order _ rfl
  funext i
  fin_cases i <;> rfl

end YM.Integration.WilsonCenteredNestedTreeLeaves
