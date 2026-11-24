import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometry

/-! Finite sums over the actual child sets of a public fusion tree. Each
nonroot field has one parent seat and each leaf has one original input. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeContractionLayout
open YangMills.Hierarchy
open scoped Classical BigOperators

abbrev Slot (t : FusionTree) := Fin t.leaves ⊕ Fin t.branches

def owner (t : FusionTree) : Slot t → t.Vertex :=
  Sum.elim t.attachLeaf (fun i : Fin t.branches => t.parent i.succ)

def allSlots (t : FusionTree) : (Σ v, t.Child v) ≃ Slot t where
  toFun p := p.2.1
  invFun s := ⟨owner t s, ⟨s,rfl⟩⟩
  left_inv := by rintro ⟨v, s, hs⟩; subst v; rfl
  right_inv _ := rfl

theorem collect (t : FusionTree) (e : Fin t.branches → ℂ) :
    (∏ v : t.Vertex, ∏ s : t.Child v, Sum.elim (fun _ : Fin t.leaves => 1) e s.1) = ∏ i, e i := by
  let f : Slot t → ℂ := Sum.elim (fun _ => 1) e
  calc
    _ = ∏ s : (Σ v, t.Child v), f ((allSlots t) s) :=
      (Fintype.prod_sigma (fun s : (Σ v, t.Child v) => f ((allSlots t) s))).symm
    _ = ∏ s : Slot t, f s := (allSlots t).prod_comp f
    _ = _ := by rw [Fintype.prod_sum_type]; simp [f]

def Options (t : FusionTree) (A : Fin t.branches → Type) : Slot t → Type
  | .inl _ => Unit
  | .inr i => A i

instance optionsFinite (t : FusionTree) (A : Fin t.branches → Type) [∀ i, Fintype (A i)]
    (s : Slot t) : Fintype (Options t A s) := by
  cases s with
  | inl i => exact inferInstanceAs (Fintype Unit)
  | inr i => exact inferInstanceAs (Fintype (A i))

def slotChoice {t : FusionTree} {A : Fin t.branches → Type} (a : ∀ i, A i) :
    (s : Slot t) → Options t A s
  | .inl _ => ()
  | .inr i => a i

def parentChoices (t : FusionTree) (A : Fin t.branches → Type) :
    ((i : Fin t.branches) → A i) ≃ ((v : t.Vertex) → (s : t.Child v) → Options t A s.1) where
  toFun a _ s := slotChoice a s.1
  invFun a i := a (t.parent i.succ) ⟨.inr i,rfl⟩
  left_inv _ := rfl
  right_inv a := by
    funext v s
    obtain ⟨s, hs⟩ := s
    subst v
    cases s with
    | inl i => exact @Subsingleton.elim Unit inferInstance _ _
    | inr i => rfl

theorem distribute (t : FusionTree) (A : Fin t.branches → Type) [∀ i, Fintype (A i)]
    (R : (v : t.Vertex) → ((s : t.Child v) → Options t A s.1) → ℂ) :
    (∑ a : ∀ i, A i, ∏ v : t.Vertex, R v (fun s => slotChoice a s.1)) =
      ∏ v : t.Vertex, ∑ q : (s : t.Child v) → Options t A s.1, R v q := by
  rw [Fintype.prod_sum]
  exact Fintype.sum_equiv (parentChoices t A) _ _ (fun _ => rfl)

def rootChoices (t : FusionTree) (B : t.Vertex → Type) :
    ((v : t.Vertex) → B v) ≃ B 0 × ((i : Fin t.branches) → B i.succ) where
  toFun f := (f 0, fun i => f i.succ)
  invFun f := Fin.cases f.1 f.2
  left_inv f := funext (Fin.cases rfl (fun _ => rfl))
  right_inv f := by cases f; rfl

end YM.Integration.WilsonSharpPhysicalTreeContractionLayout
