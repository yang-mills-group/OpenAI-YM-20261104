import YM.Integration.WilsonCenteredNestedPairBill

/-! Both vertices of the genuinely ternary tree evaluate the same offered
course before summation. The single sum is over every channel of every
inner grade, including zero; no projection is made at the outer leaf. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedPairRead
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Composite
open Extraction Spec Table Filter WilsonCenteredNestedProgram WilsonCenteredNestedTwoVertex
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def branches (h d : ℕ) : Branches F Q (f:=arms) (rollCaps (caps h d)) ≃ Menu.Cut Q d where
  toFun j := j 0
  invFun j i := Fin.cases j (Fin.cases () (fun b=>Fin.elim0 b)) i
  left_inv j := by funext i;fin_cases i; rfl; exact Subsingleton.elim (_ : Unit) _
  right_inv _ := rfl

theorem deposited (A : Rule F Q) (g : ℝ→ℝ) (h d : ℕ) (v : full.Leaf→S.Tag)
    (z : full.Plot) (r a : ℝ) (m : ℕ) (c : Q.channels m) :
    run F Q A g full (dates r a) z v (caps h d) m ⟨Fin.last m,c⟩ =
    ∑ u : Menu.Cut Q d,
      A 2 u.1 u.2 a (g a) (skyline (childPlace 0 z)) (fun i=>v ⟨0,⟨i,()⟩⟩)
          (anchor (childPlace 0 z)) *
      A 2 m c r (g r) (skyline z)
        (echoTags F Q v ((branches F Q h d).symm u)) (anchor z) := by
  unfold WilsonCenteredNestedTwoVertex.full WilsonCenteredNestedProgram.run
  apply Fintype.sum_equiv (branches F Q h d)
  intro j
  rw [Fin.prod_univ_two]
  congr 1
  · change (∑ b : (Fin 2→Unit), (∏ _ : Fin 2,(1:ℂ)) * _) * 1 = _
    simp
    rfl
  · congr 1
    rw [Equiv.symm_apply_apply]

theorem heldTags (h d : ℕ) (v : full.Leaf→S.Tag) (u : Menu.Cut Q d) :
    echoTags F Q v ((branches F Q h d).symm u) 0 = oneTag F Q u.1 u.2 ∧
    echoTags F Q v ((branches F Q h d).symm u) 1 = v ⟨1,()⟩ := ⟨rfl,rfl⟩

end YM.Integration.WilsonCenteredNestedPairRead
