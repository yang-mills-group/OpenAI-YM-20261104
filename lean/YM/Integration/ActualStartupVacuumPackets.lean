import YM.Integration.ActualStartupRootedCurvature
import YM.Integration.ZeroAwareVacuumPackets

/-!
Actual zero-aware startup packets for the unchanged finite album.
The price is an explicit finite sum over its original ranks, with a
per-root orientation/plaquette count and the true connector exponential.
No volume factor, new regularity premise, or changed label is used.
This does not assert the stronger legacy VacuumPackets receipt.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualStartupVacuumPackets

open Function Finset Lattice Wilson RG Tensor
open WilsonStartup WilsonStartup.Start WilsonStartup.IterationFour
open ActualStartupCurvaturePackets ActualStartupRootedCurvature
open LocalComparison.Global
open scoped Classical BigOperators Matrix.Norms.Frobenius

attribute [local instance] Gauge.frobInner

variable {G : Gauge} {n : Side}

def zeroAtom (G : Gauge) (k : ℕ) : Atom G k :=
  atom G 0 ⟨(0, 1), by decide⟩ k

def sheetAtom (G : Gauge) (u : ℝ) (k : ℕ) : Sheet n → Atom G k :=
  Sum.elim (fun i => rootedAtom G u (connector i.1 i.2.2) k)
    (fun _ => zeroAtom G k)

def rowAtom (G : Gauge) (n : Side) (u : ℝ) (k : ℕ) (i : ℕ) : Atom G k :=
  if Padded.fixed (Sheet n) i then sheetAtom G u k (Padded.name (Sheet n) i)
  else zeroAtom G k

def rowCost (G : Gauge) (u width : ℝ) (k : ℕ) : ℝ :=
  |u| * coefficientCost G k * Real.exp (width * (k * 6 : ℕ))

def layerCost (G : Gauge) (u width : ℝ) (k : ℕ) : ℝ :=
  (Fintype.card Signed : ℝ) * Fintype.card PlaqAxes * rowCost G u width k

def finiteCost (G : Gauge) (S : Stage) (r : ℕ) (width : ℝ) : ℝ :=
  ((List.range (r - 2)).map
    (fun j => layerCost G (Start.weight S.clip 1) width (5 + j))).sum

def albumCost (G : Gauge) (p : BudgetPoint) (S : Stage) (r : ℕ) (width : ℝ) : ℝ :=
  max (finiteCost G S r width) (Real.exp (p.supportExponent * (5 ^ 4 : ℕ)))

private theorem zero_magnitude (k : ℕ) : (zeroAtom G k).magnitude = 0 := by
  rw [zeroAtom, atom_magnitude]
  simp

private theorem zero_unmasked (k : ℕ) (o : Site n) (U : Config G n) :
    (zeroAtom G k).unmasked U o = 0 := by
  rw [zeroAtom, atom_unmasked]
  simp

private theorem zero_budget (k : ℕ) (width : ℝ) :
    (zeroAtom G k).budget width = 0 := by
  rw [Atom.budget, zero_magnitude, zero_mul]

theorem layerCost_nonnegative (u width : ℝ) (k : ℕ) :
    0 ≤ layerCost G u width k := by
  unfold layerCost rowCost
  have h := coefficientCost_nonnegative G k
  positivity

theorem rowAtom_invariant (u : ℝ) (k : ℕ) (i : ℕ) :
    (rowAtom G n u k i).Invariant := by
  unfold rowAtom
  split
  · cases Padded.name (Sheet n) i with
    | inl a => exact rooted_invariant u (connector a.1 a.2.2) k
    | inr _ => exact atom_invariant 0 _ k
  · exact atom_invariant 0 _ k

/-- Complete literal action equality at every original Nat label, including
all blank and non-fixed padding entries. -/
theorem rowAtom_action (u : ℝ) (k : ℕ) (i : ℕ) (U : Config G n) :
    (slate G n u (terms G k)).action i U =
      (rowAtom G n u k i).unmasked U
        ((slate G n u (terms G k)).labels i).site := by
  by_cases hf : Padded.fixed (Sheet n) i
  · simp only [slate, rowAtom, hf, ↓reduceIte, Function.comp_apply]
    cases Padded.name (Sheet n) i with
    | inl a =>
        change u * element G (terms G k) a.positive U =
          (rootedAtom G u (connector a.1 a.2.2) k).unmasked U a.native
        rw [rooted_unmasked, connector_face]
    | inr a =>
        change 0 = (zeroAtom G k).unmasked U a.val.1
        exact (zero_unmasked k _ U).symm
  · simp only [slate, rowAtom, hf, ↓reduceIte, Pi.zero_apply]
    exact (zero_unmasked k _ U).symm

/-- Positive coefficient magnitude forces an active original Key; its
footprint is contained in exactly that Key's original support. -/
theorem rowAtom_support (u : ℝ) (k : ℕ) (i : ℕ)
    (hne : (rowAtom G n u k i).magnitude ≠ 0) :
    (rowAtom G n u k i).footprint
        ((slate G n u (terms G k)).labels i).site ⊆
      ((slate G n u (terms G k)).labels i).support := by
  by_cases hf : Padded.fixed (Sheet n) i
  · simp only [rowAtom, hf, ↓reduceIte] at hne ⊢
    cases hn : Padded.name (Sheet n) i with
    | inl a =>
        simpa only [slate, Function.comp_apply, hn, eInfo, Sum.elim_inl, Key.addrE,
          sheetAtom] using rooted_support u k a
    | inr a =>
        simp only [hn, sheetAtom, Sum.elim_inr] at hne
        exact False.elim (hne (zero_magnitude k))
  · exact False.elim (hne (by rw [rowAtom, if_neg hf, zero_magnitude]))

/-- Original support cover number, with zero rows kept in place and charged zero. -/
theorem rowAtom_cover (p : BudgetPoint) (u : ℝ) (k : ℕ) (i : ℕ)
    (hne : (rowAtom G n u k i).magnitude ≠ 0) :
    coverNumber p.B ((slate G n u (terms G k)).labels i).support ≤ 5 ^ 4 := by
  by_cases hf : Padded.fixed (Sheet n) i
  · simp only [rowAtom, hf, ↓reduceIte] at hne
    cases hn : Padded.name (Sheet n) i with
    | inl a =>
        simpa only [slate, Function.comp_apply, hn, eInfo, Sum.elim_inl, Key.addrE] using
          skin_cost (b := p) a
    | inr a =>
        simp only [hn, sheetAtom, Sum.elim_inr] at hne
        exact False.elim (hne (zero_magnitude k))
  · exact False.elim (hne (by rw [rowAtom, if_neg hf, zero_magnitude]))

/-- The all-row exponential sum is bounded per original root by a fixed finite
orientation/plaquette count, without a period-volume factor. -/
theorem rowAtom_exponential (u width : ℝ) (hw : 0 ≤ width) (k : ℕ) (o : Site n) :
    SumBudget
      (fun i => if ((slate G n u (terms G k)).labels i).site = o then
        (rowAtom G n u k i).magnitude *
          Real.exp (width * (rowAtom G n u k i).length) else 0)
      (layerCost G u width k) := by
  let g (a : Sheet n) :=
    if (eInfo a).site = o then (sheetAtom G u k a).budget width else 0
  refine Padded.budget (g := g) ?_ ?_ ?_
  · intro i
    by_cases hf : Padded.fixed (Sheet n) i
    · simp only [rowAtom, hf, ↓reduceIte, slate, Function.comp_apply, g, Atom.budget]
    · simp only [rowAtom, hf, ↓reduceIte, zero_magnitude, zero_mul, ite_self]
  · intro a
    unfold g
    split
    · unfold Atom.budget Atom.magnitude
      positivity
    · exact le_rfl
  · unfold g
    rw [Fintype.sum_sum_type]
    simp only [sheetAtom, Sum.elim_inl, Sum.elim_inr, zero_budget, ite_self,
      Finset.sum_const_zero, add_zero]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type (fun _ : Cell n => _)]
    rw [show layerCost G u width k =
        ∑ _s : Signed, ∑ x : Site n, ∑ _b : PlaqAxes,
          (if x = o then rowCost G u width k else 0) by
      simp [layerCost]; ring]
    refine Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun x _ =>
      Finset.sum_le_sum (fun b _ => ?_)))
    change (if x = o then (rootedAtom G u (connector s b) k).budget width else 0) ≤ _
    by_cases hx : x = o
    · rw [if_pos hx, if_pos hx]
      exact rooted_connector_budget u width hw (s, x, b) k
    · simp only [hx, ↓reduceIte]
      exact le_rfl

theorem albumCost_positive (p : BudgetPoint) (S : Stage) (r : ℕ) (width : ℝ) :
    0 < albumCost G p S r width :=
  (Real.exp_pos _).trans_le (le_max_right _ _)

/-- A concrete receipt for the unchanged original album. Only nonnegative
chosen width is assumed; every represented row and every finite cost is constructed. -/
def albumPackets (G : Gauge) (n : Side) (p : BudgetPoint) (S : Stage) (r : ℕ)
    (width : ℝ) (hw : 0 ≤ width) :
    ZeroAwareVacuumPackets (album G n p S r) p (r + 2) width
      (albumCost G p S r width) where
  atom a := rowAtom G n (Start.weight S.clip 1) a.rank
  rank_bounded a ha := album_rank_bounded p S r a ha
  invariant a _ i := rowAtom_invariant (Start.weight S.clip 1) a.rank i
  original_action a ha i U := by
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    exact rowAtom_action (Start.weight S.clip 1) (5 + j) i U
  support a ha i hne := by
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    exact rowAtom_support (Start.weight S.clip 1) (5 + j) i hne
  pieceCost a := layerCost G (Start.weight S.clip 1) width a.rank
  piece_cost_nonnegative a _ := layerCost_nonnegative (Start.weight S.clip 1) width a.rank
  exponential a ha o := by
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    exact rowAtom_exponential (Start.weight S.clip 1) width hw (5 + j) o
  total := by
    rw [album, List.map_map]
    change finiteCost G S r width ≤ albumCost G p S r width
    exact le_max_left _ _
  coverOffset := 5 ^ 4
  coverSlope := 0
  cover a ha i hne := by
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    have h := rowAtom_cover p (Start.weight S.clip 1) (5 + j) i hne
    have hR : (coverNumber p.B
        ((slate G n (Start.weight S.clip 1) (terms G (5 + j))).labels i).support : ℝ) ≤
        (5 ^ 4 : ℕ) := by exact_mod_cast h
    simpa only [top_terms, Nat.cast_zero, zero_mul, add_zero, mul_comm] using
      mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg p.B)
  width_reserved := by
    simpa only [Nat.cast_zero, mul_zero, zero_div] using
      div_nonneg hw (by norm_num : (0 : ℝ) ≤ 4)
  cover_cost := le_max_right _ _

/-- The constructed family uses the exact original layers; its atom map and
finite price are explicit, without an alternative representation premise. -/
theorem albumPackets_data (p : BudgetPoint) (S : Stage) (r : ℕ)
    (width : ℝ) (hw : 0 ≤ width) :
    (albumPackets G n p S r width hw).atom =
        (fun a : YM.IterationFour.Vacuum.Piece G n =>
          rowAtom G n (Start.weight S.clip 1) a.rank) ∧
      (albumPackets G n p S r width hw).pieceCost =
        (fun a : YM.IterationFour.Vacuum.Piece G n =>
          layerCost G (Start.weight S.clip 1) width a.rank) ∧
      (albumPackets G n p S r width hw).coverOffset = 5 ^ 4 ∧
      (albumPackets G n p S r width hw).coverSlope = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

end YM.Integration.ActualStartupVacuumPackets
end
