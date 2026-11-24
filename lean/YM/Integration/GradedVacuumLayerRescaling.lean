import YM.Integration.NativeVacuumLayerRescaling

/-!
# The complete graded receipt for the same scaled vacuum list

The original atom witness is recovered through the exact inverse on Piece,
including its credit field. No selection of a different preimage, deletion of
duplicates or replacement of zero rows is needed. The only enlarged scalar
budget is the explicit max(ratio^-2, ratio^order). The original BudgetPoint,
width, cover constants, paths and reserve inequality are all retained.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.GradedVacuumLayerRescaling

open Function Finset Lattice Wilson RG
open YM.IterationFour.Vacuum
open LocalComparison.Global FullQLocal NativeVacuumLayerRescaling
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side}

/-- Scale the actual coefficient array of an atom, keeping every leg. -/
def atom {k : ℕ} (c : ℝ) (a : Atom G k) : Atom G k where
  leg := a.leg
  coeff b := c * a.coeff b

private theorem atom_poly {k : ℕ} (c : ℝ) (a : Atom G k)
    (x : Fin k → G.Color) : (atom c a).poly x = c * a.poly x := by
  simp only [atom, Atom.poly, Finset.mul_sum, mul_assoc]

private theorem atom_invariant {k : ℕ} (c : ℝ) (a : Atom G k)
    (ha : a.Invariant) : (atom c a).Invariant := by
  intro u x
  rw [atom_poly, atom_poly, ha]

private theorem atom_magnitude {k : ℕ} (c : ℝ) (a : Atom G k) :
    (atom c a).magnitude = ‖c‖ * a.magnitude := by
  simp only [atom, Atom.magnitude, abs_mul, Real.norm_eq_abs, Finset.mul_sum]

private theorem atom_unmasked {k : ℕ} (c : ℝ) (a : Atom G k)
    (U : Config G n) (o : Site n) :
    (atom c a).unmasked U o = c * a.unmasked U o :=
  atom_poly c a _

private theorem atom_length {k : ℕ} (c : ℝ) (a : Atom G k) :
    (atom c a).length = a.length := rfl

private theorem atom_footprint {k : ℕ} (c : ℝ) (a : Atom G k)
    (o : Site n) : (atom c a).footprint o = a.footprint o := rfl

private theorem sum_mono {ι : Type*} (S : List ι) (f g : ι → ℝ)
    (h : ∀ a ∈ S, f a ≤ g a) : (S.map f).sum ≤ (S.map g).sum := by
  induction S with
  | nil => exact le_rfl
  | cons a S ih =>
      exact add_le_add (h a (by simp))
        (ih (fun b hb => h b (by simp [hb])))

variable {S : List (Piece G n)} {p : BudgetPoint} {order rankCap : ℕ}
    {width budget : ℝ} (H : GradedVacuumLayers S p order rankCap width budget)

/-- The inverse has the same literal rank, so this is an atom of a.rank. -/
def scaledAtom (ratio : ℝ) (a : Piece G n) (i : ℕ) : Atom G a.rank :=
  atom (factor ratio a) (H.packets.atom (piece ratio⁻¹ a) i)

def scaledCost (ratio : ℝ) (a : Piece G n) : ℝ :=
  ‖factor ratio a‖ * H.packets.pieceCost (piece ratio⁻¹ a)

private theorem scaledAtom_piece {ratio : ℝ} (hr : ratio ≠ 0)
    (a : Piece G n) (i : ℕ) :
    scaledAtom H ratio (piece ratio a) i =
      atom (factor ratio a) (H.packets.atom a i) := by
  have hatom (b c : Piece G n) (h : b = c) :
      HEq (H.packets.atom b i) (H.packets.atom c i) := by
    cases h
    rfl
  change atom (factor ratio a)
      (H.packets.atom (piece ratio⁻¹ (piece ratio a)) i) =
    atom (factor ratio a) (H.packets.atom a i)
  exact congrArg (fun t : Atom G a.rank => atom (factor ratio a) t)
    (eq_of_heq (hatom _ _ (inverse hr a)))

private theorem scaledCost_piece {ratio : ℝ} (hr : ratio ≠ 0)
    (a : Piece G n) :
    scaledCost H ratio (piece ratio a) =
      ‖factor ratio a‖ * H.packets.pieceCost a := by
  unfold scaledCost
  rw [factor_piece, inverse hr]

/-- All zero-aware fields, not just rank or analyticity, survive. -/
def packets {ratio : ℝ} (hr : 0 < ratio) :
    ZeroAwareVacuumPackets (layers ratio S) p rankCap width
      (factorBound ratio order * budget) where
  atom := scaledAtom H ratio
  rank_bounded a ha := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact H.packets.rank_bounded b hb
  invariant a ha i := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rw [scaledAtom_piece H hr.ne']
    exact atom_invariant _ _ (H.packets.invariant b hb i)
  original_action a ha i U := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rw [scaledAtom_piece H hr.ne']
    change factor ratio b * b.packet.action i U =
      (atom (factor ratio b) (H.packets.atom b i)).unmasked U (b.packet.labels i).site
    rw [atom_unmasked]
    rw [H.packets.original_action b hb i U]
  support a ha i hne := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rw [scaledAtom_piece H hr.ne'] at hne
    change (atom (factor ratio b) (H.packets.atom b i)).magnitude ≠ 0 at hne
    rw [atom_magnitude] at hne
    have hn : (H.packets.atom b i).magnitude ≠ 0 := by
      intro hz
      exact hne (by rw [hz, mul_zero])
    rw [scaledAtom_piece H hr.ne']
    change (atom (factor ratio b) (H.packets.atom b i)).footprint (b.packet.labels i).site ⊆
      (b.packet.labels i).support
    rw [atom_footprint]
    exact H.packets.support b hb i hn
  pieceCost := scaledCost H ratio
  piece_cost_nonnegative a ha := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rw [scaledCost_piece H hr.ne']
    exact mul_nonneg (norm_nonneg _) (H.packets.piece_cost_nonnegative b hb)
  exponential a ha o := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    simp only [scaledAtom_piece H hr.ne', scaledCost_piece H hr.ne']
    dsimp only [piece, payload]
    simp only [atom_magnitude, atom_length]
    have hh := YM.Push.AbsoluteSums.budget_scale
      (norm_nonneg (factor ratio b)) (H.packets.exponential b hb o)
    simpa only [piece, payload, mul_ite, mul_zero, mul_assoc] using hh
  total := by
    change ((S.map (piece ratio)).map (scaledCost H ratio)).sum ≤ _
    simp only [List.map_map, Function.comp_def, scaledCost_piece H hr.ne']
    calc
      (S.map (fun a => ‖factor ratio a‖ * H.packets.pieceCost a)).sum ≤
          (S.map (fun a => factorBound ratio order * H.packets.pieceCost a)).sum :=
        sum_mono S _ _ (fun a ha => mul_le_mul_of_nonneg_right
          ((factor_bound hr H).2 a ha) (H.packets.piece_cost_nonnegative a ha))
      _ = factorBound ratio order * (S.map H.packets.pieceCost).sum :=
        List.sum_map_mul_left _ _ _
      _ ≤ factorBound ratio order * budget :=
        mul_le_mul_of_nonneg_left H.packets.total
          (zero_le_one.trans (factor_bound hr H).1)
  coverOffset := H.packets.coverOffset
  coverSlope := H.packets.coverSlope
  cover a ha i hne := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rw [scaledAtom_piece H hr.ne'] at hne
    change (atom (factor ratio b) (H.packets.atom b i)).magnitude ≠ 0 at hne
    rw [atom_magnitude] at hne
    have hn : (H.packets.atom b i).magnitude ≠ 0 := by
      intro hz
      exact hne (by rw [hz, mul_zero])
    rw [scaledAtom_piece H hr.ne']
    change (p.B : ℝ) * coverNumber p.B (b.packet.labels i).support ≤
      H.packets.coverOffset * (p.B : ℝ) +
        H.packets.coverSlope * (atom (factor ratio b) (H.packets.atom b i)).length
    rw [atom_length]
    exact H.packets.cover b hb i hn
  width_reserved := H.packets.width_reserved
  cover_cost := by
    have hb : 0 ≤ budget :=
      (le_of_lt (Real.exp_pos _)).trans H.packets.cover_cost
    refine H.packets.cover_cost.trans ?_
    calc
      budget = 1 * budget := by ring
      _ ≤ factorBound ratio order * budget :=
        mul_le_mul_of_nonneg_right (factor_bound hr H).1 hb

/-- The original requested order/rank and positive-width inlet are unchanged;
only the displayed, fixed-ratio scalar budget is enlarged. -/
def graded {ratio : ℝ} (hr : 0 < ratio) :
    GradedVacuumLayers (layers ratio S) p order rankCap width
      (factorBound ratio order * budget) where
  packets := packets H hr
  orders a ha := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact H.orders b hb
  leading_rank a ha := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact H.leading_rank b hb

/-- Per-occurrence cost is exact; no maximum rank replaces its own factor. -/
theorem exact_cost {ratio : ℝ} (hr : 0 < ratio) (a : Piece G n) :
    (graded H hr).packets.pieceCost (piece ratio a) =
      ‖factor ratio a‖ * H.packets.pieceCost a :=
  scaledCost_piece H hr.ne' a

end YM.Integration.GradedVacuumLayerRescaling
end
