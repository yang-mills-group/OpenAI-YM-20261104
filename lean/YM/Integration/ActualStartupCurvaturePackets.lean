import YM.IterationFour.Shore.Rose
import YM.Integration.LocalComparisonGlobalContract

/-!
Exact curvature atoms for the original startup terms, and the support
restriction imposed by the current VacuumPackets type. No original padded
row, label or action is removed or changed. The atom value identity below is
at the actual plaquette root; it does not identify that root with every
oriented row's stored native root.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualStartupCurvaturePackets

open Function Finset Lattice Wilson RG Tensor
open WilsonStartup WilsonStartup.Start WilsonStartup.IterationFour
open LocalComparison.Global
open scoped Classical BigOperators Matrix.Norms.Frobenius

attribute [local instance] Gauge.frobInner

variable {G : Gauge} {n : Side} {k : ℕ}

def atom (G : Gauge) (u : ℝ) (b : PlaqAxes) (k : ℕ) : Atom G k :=
  Design.extractAtom G b (u • coeff (inK G) k 0)

def coefficientCost (G : Gauge) (k : ℕ) : ℝ :=
  ∑ v : Fin k → G.ColorIndex,
    |coeff (inK G) k 0 (fun i => EuclideanSpace.basisFun G.ColorIndex ℝ (v i))|

theorem coefficientCost_nonnegative (G : Gauge) (k : ℕ) :
    0 ≤ coefficientCost G k :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- The original Taylor tensor is invariant on all independent color slots. -/
theorem atom_invariant (u : ℝ) (b : PlaqAxes) (k : ℕ) :
    (atom G u b k).Invariant := by
  apply Design.extract_invariant
  intro v x
  change u * coeff (inK G) k 0 (fun i => G.adjoint v (x i)) =
    u * coeff (inK G) k 0 x
  rw [coeff_adjoint]

/-- This is the original curvature term, with its actual scalar coefficient. -/
theorem atom_unmasked (u : ℝ) (b : PlaqAxes) (k : ℕ)
    (o : Site n) (U : Config G n) :
    (atom G u b k).unmasked U o =
      u * element G (terms G k) (o, b) U := by
  rw [atom, Design.extract_unmasked]
  change u * coeff (inK G) k 0 (fun _ => G.curvature (faceValue U (o, b))) =
    u * coeff (inK G) k 0 (fun _ => Quad.kMat (G.mat (faceValue U (o, b))))
  rw [Quad.k_actual]

/-- True covering-path length, not torus distance. -/
theorem atom_length (u : ℝ) (b : PlaqAxes) (k : ℕ) :
    (atom G u b k).length = k * 4 := by
  simp [Atom.length, atom, Design.extractAtom, Design.plaquette, Slot.length]

theorem atom_magnitude (u : ℝ) (b : PlaqAxes) (k : ℕ) :
    (atom G u b k).magnitude = |u| * coefficientCost G k := by
  change (∑ v : Fin k → G.ColorIndex,
      |u * coeff (inK G) k 0
        (fun i => EuclideanSpace.basisFun G.ColorIndex ℝ (v i))|) =
    |u| * coefficientCost G k
  rw [coefficientCost, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => abs_mul _ _)

/-- The exponential cost includes every repeated plaquette leg. -/
theorem atom_budget (u width : ℝ) (b : PlaqAxes) (k : ℕ) :
    (atom G u b k).budget width =
      |u| * coefficientCost G k * Real.exp (width * (k * 4 : ℕ)) := by
  unfold Atom.budget
  rw [atom_magnitude, atom_length]

theorem atom_footprint (u : ℝ) (b : PlaqAxes) (hk : k ≠ 0) (o : Site n) :
    (atom G u b k).footprint o = touched (o, b) :=
  Design.footprint _ hk b o

/-- Every active padded row has exactly this value at its original positive
plaquette. No sum or coefficient is discarded. -/
theorem slate_active_action (u : ℝ) (k : ℕ) (i : Key n)
    (U : Config G n) :
    (slate G n u (terms G k)).action
        (Padded.index (Sum.inl i : Sheet n)) U =
      (atom G u i.positive.2 k).unmasked U i.positive.1 := by
  calc
    _ = u * element G (terms G k) i.positive U := by simp [slate]
    _ = _ := (atom_unmasked u i.positive.2 k i.positive.1 U).symm

/-- The original finite album's rank bound, including every member. -/
theorem album_rank_bounded (p : BudgetPoint) (S : Stage) (r : ℕ)
    (a : YM.IterationFour.Vacuum.Piece G n) (ha : a ∈ album G n p S r) : a.rank ≤ r + 2 := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
  have hj' := List.mem_range.mp hj
  change 5 + j ≤ r + 2
  omega

/-- A literal existing blank address, not a new or enlarged support. -/
def blank (o : Site n) : Blank n :=
  ⟨(o, {o}), Finset.mem_singleton_self o⟩

def blankIndex (o : Site n) : ℕ :=
  Padded.index (Sum.inr (blank o) : Sheet n)

/-- The singleton blank row is present in every original startup slate. -/
theorem slate_blank (u : ℝ) (f : G.Mat → ℝ) (o : Site n) :
    ((slate G n u f).labels (blankIndex o)).site = o ∧
    ((slate G n u f).labels (blankIndex o)).support = {o} ∧
    (slate G n u f).action (blankIndex o) = 0 := by
  simp [blankIndex, blank, slate, eInfo]

private theorem slot_base_mem (s : Slot) : s.offset ∈ s.stencil := by
  simp [Slot.stencil, square, visits]

private theorem slot_next_mem (s : Slot) :
    s.offset + step s.plaq.val.1 ∈ s.stencil := by
  simp [Slot.stencil, square, visits]

/-- Every native Slot contains a genuine plaquette, even if its walk is
empty and its coefficient is zero. This prevents singleton support at
positive rank on a nontrivial torus. -/
theorem atom_not_singleton (a : Atom G k) (hk : 0 < k)
    (hn : 1 < n.val) (o : Site n) : ¬ a.footprint o ⊆ {o} := by
  intro hs
  let i : Fin k := ⟨0, hk⟩
  let s : Slot := a.leg i
  have hm (z : Cover) (hz : z ∈ s.stencil) :
      wrap n z + o ∈ a.footprint o := by
    apply Finset.mem_image.mpr
    refine ⟨z, Finset.mem_insert_of_mem ?_, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hz⟩
  have h0 : wrap n s.offset + o = o :=
    Finset.mem_singleton.mp (hs (hm _ (slot_base_mem s)))
  have h1 : wrap n (s.offset + step s.plaq.val.1) + o = o :=
    Finset.mem_singleton.mp (hs (hm _ (slot_next_mem s)))
  rw [map_add] at h1
  have hh : wrap n s.offset + wrap n (step s.plaq.val.1) = wrap n s.offset :=
    add_right_cancel (h1.trans h0.symm)
  have he : wrap n (step s.plaq.val.1) = 0 :=
    add_left_cancel (hh.trans (add_zero _).symm)
  rw [wrap_step] at he
  have hz : (1 : ZMod n.val) = 0 := by
    simpa only [step_apply, ↓reduceIte, Pi.zero_apply] using
      congrFun he s.plaq.val.1
  letI : Fact (1 < n.val) := ⟨hn⟩
  exact one_ne_zero hz

/-- The current unconditional support field is incompatible with the
original positive-rank album's singleton blank row. This diagnoses the
existing record; it does not change that record or the original slate. -/
theorem no_album_vacuumPackets (p : BudgetPoint) (S : Stage) (r rankCap : ℕ)
    (width budget : ℝ) (hn : 1 < n.val) (hr : 2 < r) :
    ¬ Nonempty (VacuumPackets (album G n p S r) p rankCap width budget) := by
  rintro ⟨P⟩
  let a := top_terms G n p S 0
  have ha : a ∈ album G n p S r :=
    List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩
  let j := blankIndex (0 : Site n)
  have hb := slate_blank (G := G) (Start.weight S.clip 1) (terms G 5) (0 : Site n)
  have hs := P.support a ha j
  change (P.atom a j).footprint
      ((slate G n (Start.weight S.clip 1) (terms G 5)).labels j).site ⊆
    ((slate G n (Start.weight S.clip 1) (terms G 5)).labels j).support at hs
  rw [hb.1, hb.2.1] at hs
  exact atom_not_singleton (P.atom a j) (by change 0 < 5 + 0; omega) hn 0 hs

end YM.Integration.ActualStartupCurvaturePackets
end
