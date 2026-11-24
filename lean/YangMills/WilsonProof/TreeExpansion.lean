import YangMills.WilsonProof.TreeProducts

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry.Contraction
open Function OPE OPE.Orbits OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Composite Spec Table
open scoped Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (Q : Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

theorem shotSum (t : Nesting.Tree) (z : t.Plot) (v : t.Leaf → S.Tag) (D : t.Inner → ℕ)
    (k : Stage F Q (boundNow t D) t) :
    nShot F Q t (still z) v D k () =
      ∑ u : Picks F Q t D, product F Q t z v (select F Q t D (boundNow t D) k u) := by
  induction t with
  | bud =>
    letI : Unique (Picks F Q bud D) := ⟨⟨fun j => nomatch j⟩, fun p => by funext j; exact nomatch j⟩
    rw [Fintype.sum_unique]
    change (1 : ℂ) = ∏ j : Empty, cell F Q bud z v _ j
    simp
  | fork n f ih =>
    let Child := (i : Fin n) → Picks F Q (f i) (childAge i D)
    let A := Branches F Q (f := f) (rollCaps D)
    let term (p : A) (u : Child) :=
      (∏ i, product F Q (f i) (childPlace i z) (childWages i v)
        (select F Q (f i) (childAge i D) (rollCaps D i) (p i) (u i))) * factor F Q (still z) v p k.2 ()
    symm
    calc
      _ = ∑ p : A × Child, term p.1 p.2 := Fintype.sum_equiv (distribute F Q D) _ _
        (product_chosen F Q z v D (boundNow (fork n f) D) k)
      _ = _ := by
        rw [Fintype.sum_prod_type]
        unfold nShot
        refine Finset.sum_congr rfl fun p _ => ?_
        unfold term
        dsimp only
        let each (i : Fin n) (u : Picks F Q (f i) (childAge i D)) := product F Q (f i)
          (childPlace i z) (childWages i v) (select F Q (f i) (childAge i D) (rollCaps D i) (p i) u)
        rw [← Finset.sum_mul]
        change (∑ r : Child, ∏ i, each i (r i)) * _ = _
        rw [← Fintype.prod_sum each]
        exact congrArg (· * _) (Finset.prod_congr rfl fun i _ => (ih i _ _ _ (p i)).symm)

/-- The outer cutoff belongs to the output request. All proper cutoffs
remain those of the given tree. -/
theorem chordSum {n : ℕ} {f : Fin n → Nesting.Tree} (z : (fork n f).Plot)
    (v : (fork n f).Leaf → S.Tag) (D : (fork n f).Inner → ℕ) (m : ℕ) (c : Q.channels m) :
    Kernel.chord F Q z v c D = ∑ u : Picks F Q (fork n f) D,
      product F Q (fork n f) z v (select F Q (fork n f) D m ⟨Fin.last m,c⟩ u) := by
  let caps : (fork n f).Inner → ℕ := Sum.elim (fun _ => m) (fun i => D (.inr i))
  have sum := shotSum F Q (fork n f) z v caps ⟨Fin.last m,c⟩
  rw [nShot] at sum
  unfold Kernel.chord stacked
  refine sum.trans (Finset.sum_congr rfl fun u _ => ?_)
  apply congrArg (product F Q (fork n f) z v)
  funext j
  rcases j with ⟨⟩ | j <;> rfl

end YM.Integration.WilsonSharpPhysicalTreeGeometry.Contraction
