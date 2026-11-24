import YM.Integration.PeriodicMarkedWinding
import YM.WilsonCoeffUV.Marked.Capture.Draw

/-! The winding allowance in the strong rooted address norm. One independent
relative lift is selected for every specified marked site and field argument.
All degrees of polynomial address weight remain available. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.RootedPeriodicMarkedWinding
open Function Set Filter Lattice Laurent Bloch RG Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Winding
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open scoped BigOperators Classical

variable {ι α V : Type} [DecidableEq ι] {S : Finset ι} {o : ι} {n : Side} {j : ℕ} {σ B : ℝ}

def Section (n : Side) (S : Finset ι) (o : ι) (p : ι → Cover) : Prop :=
  ∀ i ∈ S, p i = p o + lift (wrap n (p i) - wrap n (p o))

/-- Extend by zero outside the section chosen relative to the one named
source. Every periodic field and marked address has a representative. -/
def row [Zero V] (n : Side) (S : Finset ι) (o : ι) (P : (ι → Site n) → Ten V (Co n α) j)
    (p : ι → Cover) (x : dock Cover α j) : V :=
  if Section n S o p ∧ unfoldAt (p o) (slideC n x) = x then P (wrap n ∘ p) (slideC n x) else 0

omit [DecidableEq ι] in
theorem reads [Zero V] (n : Side) (S : Finset ι) (o : ι) (P : (ι → Site n) → Ten V (Co n α) j)
    (z : ι → Site n) (x : dock (Site n) α j) :
    let p := PeriodicMarkedWinding.roots n z o
    row n S o P p (unfoldAt (p o) x) = P z x := by
  intro p
  have hw : wrap n ∘ p = z := PeriodicMarkedWinding.roots_wrap z o
  have hs : Section n S o p := by
    intro i _
    rw [show wrap n (p i) = z i from congr_fun hw i, show wrap n (p o) = z o from congr_fun hw o]
    simp [p, PeriodicMarkedWinding.roots]
  simp only [row, slides_back, hs, true_and, if_true, hw]

omit [DecidableEq ι] in
private theorem rootedSyn (ho : o ∈ S) (p : ι → Cover) (hp : Section n S o p)
    (x : dock (Site n) α j) :
    Syn terrain p S (unfoldAt (p o) x) ≤ 2 * Syn (tor n) (wrap n ∘ p) S x := by
  apply league_cash _ (a:=p o)
  intro i
  cases i with
  | inl i =>
    change size (p i.val - p o) ≤ _
    rw [hp i.val i.property, add_sub_cancel_left]
    exact leg_le (tor n) (foyer (wrap n ∘ p) S x) (.inl ⟨o,ho⟩) (.inl i)
  | inr i =>
    rw [show foyer p S _ _ = ((unfoldAt (p o) x) i).1 from rfl, near_change]
    exact leg_le (tor n) (foyer (wrap n ∘ p) S x) (.inl ⟨o,ho⟩) (.inr i)

omit [DecidableEq ι] in
theorem lifted [NormedAddCommGroup V] (ho : o ∈ S) (hs : 0 ≤ σ)
    (P : (ι → Site n) → Ten V (Co n α) j) (hP : ∀ z, Wig (tor n) z σ B S (P z)) (p : ι → Cover) :
    Wig terrain p (σ/2) B S (row n S o P p) := by
  obtain ⟨hb, h⟩ := hP (wrap n ∘ p)
  refine ⟨hb, fun x => ?_⟩
  unfold row
  split
  next hh =>
    have hc := rootedSyn ho p hh.1 (slideC n x)
    rw [hh.2] at hc
    apply (h (slideC n x)).trans
    apply mul_le_mul_of_nonneg_left _ hb
    apply Real.exp_monotone
    have hr : (Syn terrain p S x : ℝ) ≤ 2*(Syn (tor n) (wrap n ∘ p) S (slideC n x) : ℝ) := by exact_mod_cast hc
    nlinarith only [mul_le_mul_of_nonneg_left hr hs]
  next => exact (norm_zero).le.trans (mul_nonneg hb (Real.exp_pos _).le)

/-- Finite joint Riesz current for each tuple of displacement and field
indices. The bill sums every independent tuple and retains an arbitrary
moment of its line length, in addition to the exponential root/field weight. -/
theorem addresses [Fintype α] {D : ι → ℕ} (ho : o ∈ S) (hs : 0 < σ)
    (P : (ι → Site n) → Ten (Pen D S) (Co n α) j) (hP : ∀ z, Wig (tor n) z σ B S (P z))
    (W : Credit) {y : ℝ} (hw : (σ/2)⁻¹ ≤ W.buy y) (hy : 1 ≤ y) (d : ℕ) :
    PostMark S o j (row n S o P) (σ/2/2) (B*(riding α j d S o W).buy y) d :=
  directV S ho _ (lifted ho hs.le P hP) hw (half_pos hs) hy d

/-- The original marked winding comparison supplies this strong measure
estimate for every periodic order and configuration of all named vertices. -/
theorem measured [Fintype α] {D : ι → ℕ} (ho : o ∈ S) (hs : 0 < σ)
    (F : (ι → Site n) → Ten (Pen D S) (Cloth α) j) (P : (ι → Site n) → Ten (Pen D S) (Co n α) j)
    (p : ∀ z, MarkU (PeriodicMarkedWinding.roots n z o) S (P z) (F z) σ B)
    (W : Credit) {y : ℝ} (hw : (σ/32/2/2)⁻¹ ≤ W.buy y) (hy : 1 ≤ y) (d : ℕ) :
    let f := fun z => Carp.plume (F z) n - P z
    let c := ((priceM α j σ + tiePay α j (σ/4) + 1)*B+B)*catchW (σ/32/16) n
    PostMark S o j (row n S o f) (σ/32/2/2/2) (c*(riding α j d S o W).buy y) d :=
  addresses ho (by positivity) _ (fun z => PeriodicMarkedWinding.periodized z o ho hs (p z)) W hw hy d

end YM.Integration.RootedPeriodicMarkedWinding
end
