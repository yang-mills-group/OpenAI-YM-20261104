import YM.Integration.WilsonCenteredNestedProducts

/-! Evaluate a signed local prescription at each native comparable vertex.
The full below-horizon label family and the one common root are the
actual original choices in `Composite.stacked`. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedProgram
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Composite
open Extraction Spec Table OPE.Nesting.Atom
open scoped Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

/-- Each call receives its own positive radius, the actual running coupling
evaluated at that radius, and all true lower-grade tokens. -/
abbrev Rule := (n m : ℕ) → Q.channels m → ℝ → ℝ → (Fin n → E4) → (Fin n → S.Tag) → E4 → ℂ

def measured : Rule F Q := fun _ m c _ _ x v o=> express Q m c x v o

def run (A : Rule F Q) (g : ℝ → ℝ) :
    (t : Tree) → (t.Inner → ℝ) → t.Plot → (t.Leaf → S.Tag) → (t.Inner → ℕ) →
      (H : ℕ) → Stage F Q H t → ℂ
  | bud,_,_,_,_,_,_ => 1
  | fork n p,s,z,v,D,_,k =>
    ∑ j : Branches F Q (f:=p) (rollCaps D),
      (∏ i,run A g (p i) (childAge i s) (childPlace i z) (childWages i v)
        (childAge i D) (rollCaps D i) (j i)) *
      A n k.1 k.2 (s (.inl ())) (g (s (.inl ()))) (skyline z) (echoTags F Q v j) (anchor z)

theorem shot (g : ℝ → ℝ) (t : Tree) (s : t.Inner → ℝ) (z : t.Plot)
    (v : t.Leaf → S.Tag) (D : t.Inner → ℕ) (k : Stage F Q (boundNow t D) t) :
    run F Q (measured F Q) g t s z v D (boundNow t D) k =
      nShot F Q t (still z) v D k () := by
  induction t with
  | bud => rfl
  | fork n p ih =>
    unfold run nShot
    refine Finset.sum_congr rfl (fun j _=>?_ )
    refine congrArg (· * _) (Finset.prod_congr rfl (fun i _=>?_))
    exact ih i _ _ _ _ _

theorem chord (g : ℝ → ℝ) {n : ℕ} {p : Fin n → Tree}
    (s : (fork n p).Inner → ℝ) (z : (fork n p).Plot) (v : (fork n p).Leaf → S.Tag)
    (D : (fork n p).Inner → ℕ) (m : ℕ) (c : Q.channels m) :
    run F Q (measured F Q) g (fork n p) s z v D m ⟨Fin.last m,c⟩ =
      Kernel.chord F Q z v c D := by
  unfold run Kernel.chord stacked
  refine Finset.sum_congr rfl (fun j _=>?_ )
  refine congrArg (· * _) (Finset.prod_congr rfl (fun i _=>?_))
  exact shot F Q g _ _ _ _ _ _

/-- Signed comparable-vertex invoices on the actual immediate-child
positions. Only the finitely many grades requested on this tree occur. -/
def calibrated (A : Rule F Q) (g logPrice change : ℝ → ℝ) :
    (t : Tree) → (t.Inner → ℝ) → t.Plot → (t.Leaf → S.Tag) → (t.Inner → ℕ) → ℕ → Prop
  | bud,_,_,_,_,_ => True
  | fork n p,s,z,v,D,H =>
    (∀ (j : Branches F Q (f:=p) (rollCaps D)) (m : ℕ),m ≤ H → ∀ c : Q.channels m,
      let r := s (.inl ())
      let child := echoTags F Q v j
      WilsonCenteredNestedProducts.Priced
        (express Q m c (skyline z) child (anchor z))
        (A n m c r (g r) (skyline z) child (anchor z))
        (logPrice r * (r^m / ∏ i,r^((child i).1))) (change r)) ∧
    ∀ i,calibrated A g logPrice change (p i) (childAge i s) (childPlace i z)
      (childWages i v) (childAge i D) (rollCaps D i)

end YM.Integration.WilsonCenteredNestedProgram
