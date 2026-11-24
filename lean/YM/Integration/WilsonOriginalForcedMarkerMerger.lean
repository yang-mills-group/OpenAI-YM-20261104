import YM.Integration.WilsonForcedMarkerLine

/-! The two actual hard-array mergers preserve the affine comparison of
perturbations that bear one named true label. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalForcedMarkerMerger
open Function Filter Finset Lattice Wilson RG Ac Marker QuadraticLocal QuadraticLocal.Fusion
open QuadraticLocal.Canopy QuadraticLocal.Fusion.Attached RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe
open WilsonForcedMarkerLine
open scoped Topology BigOperators Classical

variable {G : Gauge} {n : Side} {p : BudgetPoint}
    {V : Type} [DecidableEq V] {R : Marker.Census V} {o : V→Site n}
    {v : V} {q : ℂ} {T ι μ : Type*} {U W : Activities G n} {e f a r : ℝ}

def Related (v:V) (q:ℂ) {P:ℕ→ForcedAddress G n} {k:Code G n}
    (A B C:Hard T p P k o R) : Prop := ∀ t i Z,Line v q (A.hard t i Z) (B.hard t i Z) (C.hard t i Z)

theorem stock {X : Shelf G n ι μ} (A B C:X.Stock p R o) (Z:Config G n)
    (h:∀ i,Line v q (A.ink i Z) (B.ink i Z) (C.ink i Z)) (i:X.Patch) :
    Line v q (A.cargo i Z) (B.cargo i Z) (C.cargo i Z) :=
  merged X.frame (flags p.threshold Z) (fun j=>A.ink j Z) (fun j=>B.ink j Z) (fun j=>C.ink j Z) h i

theorem first [Fintype V] (A B C:Hard T p U.forced U.K o R)
    (h:Related v q A B C) (D:Kiosk.First p U W e f a) :
    Related v q (Kiosk.First.led A D) (Kiosk.First.led B D) (Kiosk.First.led C D) := by
  intro t i Z
  apply stock (((Kiosk.shape D.oldP D.oldV A).stock D.softens) t)
    (((Kiosk.shape D.oldP D.oldV B).stock D.softens) t)
    (((Kiosk.shape D.oldP D.oldV C).stock D.softens) t) Z _ (toPatch D.roll i)
  rintro (j|j)
  · exact h t j Z
  · exact same _

theorem readdress {U W:Activities G n} {A B C:Hard T p U.forced U.K o R} (h:Related v q A B C)
    {F K:ℕ↪ℕ} (D:Readdress p F K U W) :
    Related v q (A.readdress D) (B.readdress D) (C.readdress D) := by
  intro t i Z
  change Line v q (stuff K (A.hard t) i Z) (stuff K (B.hard t) i Z) (stuff K (C.hard t) i Z)
  by_cases hi:i∈Set.range K
  · obtain ⟨x,rfl⟩:=hi
    simp only [stuffed]; exact h t x Z
  · rw [blank _ _ hi,blank _ _ hi,blank _ _ hi]
    exact same _

theorem second [Fintype V] [Countable ι] (A B C:Hard T p U.forced U.K o R)
    (h:Related v q A B C) (M:ShiftRows T ι G p o R) (D:Kiosk.Second p U W e f a r) :
    Related v q (Kiosk.Second.canopy A M D) (Kiosk.Second.canopy B M D)
        (Kiosk.Second.canopy C M D) := by
  intro t i Z
  let a₀:=Kiosk.shape D.oldP D.oldV A
  let a₁:=Kiosk.shape D.oldP D.oldV B
  let a₂:=Kiosk.shape D.oldP D.oldV C
  apply stock (M.stock D.softens a₀ t) (M.stock D.softens a₁ t) (M.stock D.softens a₂ t)
    Z _ (toPatch (folio G n) i)
  rintro (j|j)
  · have h0 : Related v q a₀ a₁ a₂ := h
    exact readdress (U:=D.skeleton.pours D.tap) h0 (Rack.preserves D.skeleton D.tap p) t j Z
  · exact same _

end YM.Integration.WilsonOriginalForcedMarkerMerger
end
