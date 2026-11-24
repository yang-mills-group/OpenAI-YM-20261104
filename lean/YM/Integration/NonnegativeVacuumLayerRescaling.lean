import YM.Integration.GradedVacuumLayerRescaling

/-!
# Zero and nonnegative fixed ratios

At ratio zero the native integer power keeps exactly the step-order-zero
payloads and zeros all other payloads. The original list occurrences and
row labels remain. Auxiliary atom witnesses for a zeroed payload may use
zero coefficient arrays; unlike the positive-ratio inverse construction,
this certificate does not assert recovery of each old zeroed atom's legs.
The complete original physical function is still given by the exact map.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NonnegativeVacuumLayerRescaling

open Function Finset Lattice Wilson RG
open YM.IterationFour.Vacuum
open LocalComparison.Global FullQLocal NativeVacuumLayerRescaling
open scoped Classical Topology BigOperators

variable {G : Gauge} {n : Side}

private def zeroAtom {k : ℕ} (a : Atom G k) : Atom G k where
  leg := a.leg
  coeff _ := 0

private theorem zero_magnitude {k : ℕ} (a : Atom G k) :
    (zeroAtom a).magnitude = 0 := by
  simp only [zeroAtom, Atom.magnitude, abs_zero, Finset.sum_const_zero]

private theorem zero_unmasked {k : ℕ} (a : Atom G k)
    (U : Config G n) (o : Site n) : (zeroAtom a).unmasked U o = 0 := by
  simp only [zeroAtom, Atom.unmasked, Atom.poly, zero_mul, Finset.sum_const_zero]

private theorem zero_invariant {k : ℕ} (a : Atom G k) :
    (zeroAtom a).Invariant := by
  intro u x
  simp only [zeroAtom, Atom.poly, zero_mul, Finset.sum_const_zero]

private theorem step_piece (ratio : ℝ) (a : Piece G n) :
    Render.stepOrder (piece ratio a) = Render.stepOrder a := rfl

private theorem factor_zero (a : Piece G n) (h : Render.stepOrder a ≠ 0) :
    factor 0 a = 0 := zero_zpow _ h

private theorem piece_zero_kept (a : Piece G n) (h : Render.stepOrder a = 0) :
    piece 0 a = a := by
  have hf : factor 0 a = 1 := by rw [factor, h, zpow_zero]
  rcases a with ⟨power, rank, ⟨labels, action⟩, credit⟩
  simp only [piece, hf, payload, one_mul, norm_one]

private theorem sum_mono {ι : Type*} (S : List ι) (f g : ι → ℝ)
    (h : ∀ a ∈ S, f a ≤ g a) : (S.map f).sum ≤ (S.map g).sum := by
  induction S with
  | nil => exact le_rfl
  | cons a S ih =>
      exact add_le_add (h a (by simp))
        (ih (fun b hb => h b (by simp [hb])))

variable {S : List (Piece G n)} {p : BudgetPoint} {order rankCap : ℕ}
    {width budget : ℝ} (H : GradedVacuumLayers S p order rankCap width budget)

private def atoms (a : Piece G n) (i : ℕ) : Atom G a.rank :=
  if Render.stepOrder a = 0 then H.packets.atom a i else zeroAtom (H.packets.atom a i)

private def cost (a : Piece G n) : ℝ :=
  if Render.stepOrder a = 0 then H.packets.pieceCost a else 0

private theorem cost_piece (a : Piece G n) :
    cost H (piece 0 a) =
      if Render.stepOrder a = 0 then H.packets.pieceCost a else 0 := by
  by_cases h : Render.stepOrder a = 0
  · rw [piece_zero_kept a h]
    rfl
  · simp only [cost, step_piece, h, if_false]

/-- All fourteen zero-aware fields are retained; zeroed payloads have zero
intrinsic cost, while every surviving payload uses its original witness. -/
def zero_packets : ZeroAwareVacuumPackets (layers 0 S) p rankCap width budget where
  atom := atoms H
  rank_bounded a ha := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact H.packets.rank_bounded b hb
  invariant a ha i := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    by_cases h : Render.stepOrder b = 0
    · rw [piece_zero_kept b h]
      simpa only [atoms, h, if_true] using H.packets.invariant b hb i
    · simpa only [atoms, step_piece, h, if_false] using
        zero_invariant (H.packets.atom (piece 0 b) i)
  original_action a ha i U := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    by_cases h : Render.stepOrder b = 0
    · rw [piece_zero_kept b h]
      simpa only [atoms, h, if_true] using H.packets.original_action b hb i U
    · simp only [atoms, step_piece, h, if_false, zero_unmasked]
      change factor 0 b * b.packet.action i U = 0
      rw [factor_zero b h, zero_mul]
  support a ha i hne := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    by_cases h : Render.stepOrder b = 0
    · rw [piece_zero_kept b h] at hne ⊢
      simp only [atoms, h, if_true] at hne ⊢
      exact H.packets.support b hb i hne
    · exfalso
      apply hne
      simp only [atoms, step_piece, h, if_false, zero_magnitude]
  pieceCost := cost H
  piece_cost_nonnegative a ha := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    rw [cost_piece H]
    split
    · exact H.packets.piece_cost_nonnegative b hb
    · exact le_rfl
  exponential a ha o := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    by_cases h : Render.stepOrder b = 0
    · rw [piece_zero_kept b h]
      simpa only [atoms, cost, h, if_true] using H.packets.exponential b hb o
    · simp only [atoms, cost, step_piece, h, if_false, zero_magnitude,
        zero_mul, ite_self]
      exact ⟨fun _ => le_rfl, summable_zero, by simp only [tsum_zero, le_refl]⟩
  total := by
    change ((S.map (piece 0)).map (cost H)).sum ≤ budget
    simp only [List.map_map, Function.comp_def, cost_piece H]
    refine (sum_mono S _ H.packets.pieceCost ?_).trans H.packets.total
    intro a ha
    split
    · exact le_rfl
    · exact H.packets.piece_cost_nonnegative a ha
  coverOffset := H.packets.coverOffset
  coverSlope := H.packets.coverSlope
  cover a ha i hne := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    by_cases h : Render.stepOrder b = 0
    · rw [piece_zero_kept b h] at hne ⊢
      simp only [atoms, h, if_true] at hne ⊢
      exact H.packets.cover b hb i hne
    · exfalso
      apply hne
      simp only [atoms, step_piece, h, if_false, zero_magnitude]
  width_reserved := H.packets.width_reserved
  cover_cost := H.packets.cover_cost

def zero_graded : GradedVacuumLayers (layers 0 S) p order rankCap width budget where
  packets := zero_packets H
  orders a ha := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact H.orders b hb
  leading_rank a ha := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact H.leading_rank b hb

/-- The zero case costs no extra amount. Positive ratios use the same
explicit inverse-square/finite-positive-power bound as before. -/
def multiplier (ratio : ℝ) (order : ℕ) : ℝ :=
  if ratio = 0 then 1 else factorBound ratio order

def nonnegative_graded {ratio : ℝ} (hr : 0 ≤ ratio) :
    GradedVacuumLayers (layers ratio S) p order rankCap width
      (multiplier ratio order * budget) := by
  by_cases hz : ratio = 0
  · subst ratio
    rw [show multiplier 0 order = 1 by simp [multiplier]]
    simpa only [one_mul] using zero_graded H
  · have hp : 0 < ratio := lt_of_le_of_ne hr (Ne.symm hz)
    simpa only [multiplier, if_neg hz] using GradedVacuumLayerRescaling.graded H hp

end YM.Integration.NonnegativeVacuumLayerRescaling
end
