import YangMills.WilsonProof.TreeChoices

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry.Contraction
open Function OPE OPE.Orbits OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Composite OPE.Nesting.Atom Spec Table
open scoped Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (Q : Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def rootField : (t : Nesting.Tree) → (t.Leaf → S.Tag) → (t.Inner → Channel F Q) → S.Tag
  | .bud, v, _ => v ()
  | .fork _ _, _, a => oneTag F Q (a (.inl ())).1 (a (.inl ())).2

theorem chosenField (t : Nesting.Tree) (v : t.Leaf → S.Tag) (D : t.Inner → ℕ) (m : ℕ)
    (k : Stage F Q m t) (u : Picks F Q t D) :
    rootField F Q t v (select F Q t D m k u) = token F Q t v k := by cases t <;> rfl

/-- The coefficient at a single inner vertex of the native tree, with all
internal channel choices fixed and the original marked leaves in place. -/
def cell : (t : Nesting.Tree) → t.Plot → (t.Leaf → S.Tag) → (t.Inner → Channel F Q) → t.Inner → ℂ
  | .bud, _, _, _, j => nomatch j
  | .fork n f, z, v, u, .inl _ =>
    express Q (u (.inl ())).1 (u (.inl ())).2 (skyline z)
      (fun i => rootField F Q (f i) (childWages i v) (childAge i u)) (anchor z)
  | .fork n f, z, v, u, .inr ⟨i,j⟩ =>
    cell (f i) (childPlace i z) (childWages i v) (childAge i u) j

def product (t : Nesting.Tree) (z : t.Plot) (v : t.Leaf → S.Tag) (u : t.Inner → Channel F Q) : ℂ :=
  ∏ j : t.Inner, cell F Q t z v u j

theorem product_fork {n : ℕ} {f : Fin n → Nesting.Tree} (z : (fork n f).Plot)
    (v : (fork n f).Leaf → S.Tag) (u : (fork n f).Inner → Channel F Q) :
    product F Q (fork n f) z v u =
      (∏ i, product F Q (f i) (childPlace i z) (childWages i v) (childAge i u)) *
        express Q (u (.inl ())).1 (u (.inl ())).2 (skyline z)
          (fun i => rootField F Q (f i) (childWages i v) (childAge i u)) (anchor z) := by
  change (∏ j : Unit ⊕ Σ i, (f i).Inner, cell F Q (fork n f) z v u j) = _
  rw [Fintype.prod_sum_type, Fintype.prod_unique, Fintype.prod_sigma]
  exact mul_comm ..

theorem product_chosen {n : ℕ} {f : Fin n → Nesting.Tree} (z : (fork n f).Plot)
    (v : (fork n f).Leaf → S.Tag) (D : (fork n f).Inner → ℕ) (m : ℕ) (k : Menu.Cut Q m)
    (u : Picks F Q (fork n f) D) :
    product F Q (fork n f) z v (select F Q (fork n f) D m k u) =
      (∏ i, product F Q (f i) (childPlace i z) (childWages i v)
        (select F Q (f i) (childAge i D) (rollCaps D i) ((distribute F Q D u).1 i)
          ((distribute F Q D u).2 i))) * factor F Q (still z) v (distribute F Q D u).1 k.2 () := by
  have child (i : Fin n) : childAge i (select F Q (fork n f) D m k u) =
      select F Q (f i) (childAge i D) (rollCaps D i) ((distribute F Q D u).1 i)
        ((distribute F Q D u).2 i) := (select_separate F Q (f i) (childAge i D) (fun j => u ⟨i,j⟩)).symm
  rw [product_fork]
  simp_rw [child, chosenField]
  rfl

end YM.Integration.WilsonSharpPhysicalTreeGeometry.Contraction
