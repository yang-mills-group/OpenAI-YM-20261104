import YangMills.WilsonProof.TreeProfiles

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open Function OPE OPE.Orbits OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Composite Spec Table
open scoped Classical BigOperators

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (Q : Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

namespace Contraction
abbrev Channel := Σ j : ℕ, Q.channels j
abbrev uncap {m : ℕ} (c : Menu.Cut Q m) : Channel F Q := ⟨c.1.val, c.2⟩

/-- Proper vertices are all inner vertices of all immediate child trees. -/
def Proper : Nesting.Tree → Type
  | .bud => Empty
  | .fork n f => Σ i : Fin n, (f i).Inner

instance properFinite (t : Nesting.Tree) : Fintype (Proper t) := by
  cases t with
  | bud => exact inferInstanceAs (Fintype Empty)
  | fork n f => exact inferInstanceAs (Fintype (Σ i : Fin n, (f i).Inner))

def inside : (t : Nesting.Tree) → Proper t → t.Inner
  | .bud, i => nomatch i
  | .fork _ _, i => .inr i

abbrev Picks (t : Nesting.Tree) (D : t.Inner → ℕ) := (j : Proper t) → Menu.Cut Q (D (inside t j))
abbrev All (t : Nesting.Tree) (D : t.Inner → ℕ) := (j : t.Inner) → Menu.Cut Q (D j)

/-- At a child fork, the channel at its own root and the proper-vertex channels
are independent finite choices. A leaf contributes the unique empty choice. -/
def separate (t : Nesting.Tree) (D : t.Inner → ℕ) :
    All F Q t D ≃ Stage F Q (boundNow t D) t × Picks F Q t D := by
  cases t with
  | bud =>
    refine ⟨(fun _ => ⟨(), (fun j => nomatch j)⟩), (fun _ j => nomatch j), ?_, ?_⟩
    · intro u; funext j; exact nomatch j
    · rintro ⟨k,rest⟩; apply Prod.ext
      · cases k; rfl
      · funext j; exact nomatch j
  | fork n f =>
    exact ⟨fun u => ⟨u (.inl ()), fun j => u (.inr j)⟩,
      fun ⟨k, rest⟩ j => match j with | .inl _ => k | .inr j => rest j,
      fun u => by funext j; rcases j with ⟨⟩ | j <;> rfl,
      fun ⟨k, rest⟩ => rfl⟩

def select : (t : Nesting.Tree) → (D : t.Inner → ℕ) → (m : ℕ) → Stage F Q m t →
    Picks F Q t D → t.Inner → Channel F Q
  | .bud, _, _, _, _, j => nomatch j
  | .fork _ _, _, _, k, _, .inl _ => uncap F Q k
  | .fork _ _, _, _, _, rest, .inr j => uncap F Q (rest j)

theorem select_separate (t : Nesting.Tree) (D : t.Inner → ℕ) (u : All F Q t D) :
    select F Q t D (boundNow t D) ((separate F Q t D u).1) ((separate F Q t D u).2) =
      fun j => uncap F Q (u j) := by
  funext j
  cases t with
  | bud => exact nomatch j
  | fork n f => rcases j with ⟨⟩ | j <;> rfl

def distribute {n : ℕ} {f : Fin n → Nesting.Tree} (D : (fork n f).Inner → ℕ) :
    Picks F Q (fork n f) D ≃
      Branches F Q (f := f) (rollCaps D) × ((i : Fin n) → Picks F Q (f i) (childAge i D)) where
  toFun u := ⟨fun i => (separate F Q (f i) (childAge i D) (fun j => u ⟨i,j⟩)).1,
              fun i => (separate F Q (f i) (childAge i D) (fun j => u ⟨i,j⟩)).2⟩
  invFun p := fun ⟨i,j⟩ => (separate F Q (f i) (childAge i D)).symm (p.1 i,p.2 i) j
  left_inv u := by
    funext ⟨i,j⟩
    exact congrFun ((separate F Q (f i) (childAge i D)).symm_apply_apply (fun j => u ⟨i,j⟩)) j
  right_inv p := by
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst ((separate F Q (f i) (childAge i D)).apply_symm_apply (p.1 i,p.2 i))
    · funext i
      exact congrArg Prod.snd ((separate F Q (f i) (childAge i D)).apply_symm_apply (p.1 i,p.2 i))

end Contraction
end YM.Integration.WilsonSharpPhysicalTreeGeometry
