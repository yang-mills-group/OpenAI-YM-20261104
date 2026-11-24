import YM.Integration.LocalComparisonGlobalContract
import YM.Integration.QLocalZeroRowConsumers

/-!
# Conservative compatibility for zero-coefficient vacuum rows

Every original layer, atom, label, support, mask and numerical budget is
retained. Only auxiliary support and cover obligations are conditional on
nonzero coefficient magnitude. A zero row's original history is not erased.

The old receipt embeds with identical data. Returning to the old receipt
requires its two unconditional geometric obligations explicitly. These
consumer lemmas change neither the old record nor any qlocal target; the
manuscript input-class bridge remains a separate implementation duty.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison.Global

open Lattice Wilson RG
open IterationFour IterationFour.Vacuum
open scoped BigOperators Classical

structure ZeroAwareVacuumPackets {G : Gauge} {n : Side} (layers : List (Piece G n))
    (p : BudgetPoint) (rankCap : ℕ) (width budget : ℝ) where
  atom : (a : Piece G n) → ℕ → Atom G a.rank
  rank_bounded a : a ∈ layers → a.rank ≤ rankCap
  invariant a : a ∈ layers → ∀ i, (atom a i).Invariant
  original_action a : a ∈ layers → ∀ i U,
    a.packet.action i U = (atom a i).unmasked U (a.packet.labels i).site
  support a : a ∈ layers → ∀ i,
    (atom a i).magnitude ≠ 0 →
    (atom a i).footprint (a.packet.labels i).site ⊆ (a.packet.labels i).support
  pieceCost : Piece G n → ℝ
  piece_cost_nonnegative a : a ∈ layers → 0 ≤ pieceCost a
  exponential a : a ∈ layers → ∀ o,
    RG.SumBudget
      (fun i : ℕ => if (a.packet.labels i).site = o then
        (atom a i).magnitude * Real.exp (width * (atom a i).length) else 0)
      (pieceCost a)
  total : (layers.map pieceCost).sum ≤ budget
  coverOffset : ℕ
  coverSlope : ℕ
  cover a : a ∈ layers → ∀ i,
    (atom a i).magnitude ≠ 0 →
    p.B * (coverNumber p.B (a.packet.labels i).support : ℝ) ≤
      coverOffset * p.B + coverSlope * (atom a i).length
  width_reserved : p.supportExponent * coverSlope / p.B ≤ width / 4
  cover_cost : Real.exp (p.supportExponent * coverOffset) ≤ budget

variable {G : Gauge} {n : Side} {layers : List (Piece G n)}
    {p : BudgetPoint} {rankCap : ℕ} {width budget : ℝ}

/-- The stronger original receipt embeds without changing any data or price. -/
def VacuumPackets.zeroAware (H : VacuumPackets layers p rankCap width budget) :
    ZeroAwareVacuumPackets layers p rankCap width budget where
  atom := H.atom
  rank_bounded := H.rank_bounded
  invariant := H.invariant
  original_action := H.original_action
  support a ha i _ := H.support a ha i
  pieceCost := H.pieceCost
  piece_cost_nonnegative := H.piece_cost_nonnegative
  exponential := H.exponential
  total := H.total
  coverOffset := H.coverOffset
  coverSlope := H.coverSlope
  cover a ha i _ := H.cover a ha i
  width_reserved := H.width_reserved
  cover_cost := H.cover_cost

/-- Recover the old receipt only when its two stronger geometric obligations
are independently available on the same atoms and original rows. -/
def ZeroAwareVacuumPackets.toStrong
    (H : ZeroAwareVacuumPackets layers p rankCap width budget)
    (hSupport : ∀ a, a ∈ layers → ∀ i,
      (H.atom a i).footprint (a.packet.labels i).site ⊆
        (a.packet.labels i).support)
    (hCover : ∀ a, a ∈ layers → ∀ i,
      p.B * (coverNumber p.B (a.packet.labels i).support : ℝ) ≤
        H.coverOffset * p.B + H.coverSlope * (H.atom a i).length) :
    VacuumPackets layers p rankCap width budget where
  atom := H.atom
  rank_bounded := H.rank_bounded
  invariant := H.invariant
  original_action := H.original_action
  support := hSupport
  pieceCost := H.pieceCost
  piece_cost_nonnegative := H.piece_cost_nonnegative
  exponential := H.exponential
  total := H.total
  coverOffset := H.coverOffset
  coverSlope := H.coverSlope
  cover := hCover
  width_reserved := H.width_reserved
  cover_cost := H.cover_cost

theorem VacuumPackets.zeroAware_data
    (H : VacuumPackets layers p rankCap width budget) :
    H.zeroAware.atom = H.atom ∧
      H.zeroAware.pieceCost = H.pieceCost ∧
      H.zeroAware.coverOffset = H.coverOffset ∧
      H.zeroAware.coverSlope = H.coverSlope :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem ZeroAwareVacuumPackets.toStrong_data
    (H : ZeroAwareVacuumPackets layers p rankCap width budget)
    (hSupport : ∀ a, a ∈ layers → ∀ i,
      (H.atom a i).footprint (a.packet.labels i).site ⊆
        (a.packet.labels i).support)
    (hCover : ∀ a, a ∈ layers → ∀ i,
      p.B * (coverNumber p.B (a.packet.labels i).support : ℝ) ≤
        H.coverOffset * p.B + H.coverSlope * (H.atom a i).length) :
    (H.toStrong hSupport hCover).atom = H.atom ∧
      (H.toStrong hSupport hCover).pieceCost = H.pieceCost ∧
      (H.toStrong hSupport hCover).coverOffset = H.coverOffset ∧
      (H.toStrong hSupport hCover).coverSlope = H.coverSlope :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem VacuumPackets.zeroAware_roundtrip
    (H : VacuumPackets layers p rankCap width budget) :
    H.zeroAware.toStrong H.support H.cover = H := by
  cases H
  rfl

theorem ZeroAwareVacuumPackets.toStrong_roundtrip
    (H : ZeroAwareVacuumPackets layers p rankCap width budget)
    (hSupport : ∀ a, a ∈ layers → ∀ i,
      (H.atom a i).footprint (a.packet.labels i).site ⊆
        (a.packet.labels i).support)
    (hCover : ∀ a, a ∈ layers → ∀ i,
      p.B * (coverNumber p.B (a.packet.labels i).support : ℝ) ≤
        H.coverOffset * p.B + H.coverSlope * (H.atom a i).length) :
    (H.toStrong hSupport hCover).zeroAware = H := by
  cases H
  rfl

/-- Geometry holds for every nonzero complete original row function; the
witness tests the fixed function, not the value at a later chosen field. -/
theorem ZeroAwareVacuumPackets.functional_support
    (H : ZeroAwareVacuumPackets layers p rankCap width budget)
    (a : Piece G n) (ha : a ∈ layers) (i : ℕ)
    (hn : ∃ U : Config G n, a.packet.action i U ≠ 0) :
    (H.atom a i).footprint (a.packet.labels i).site ⊆
      (a.packet.labels i).support := by
  apply H.support a ha i
  intro hzero
  obtain ⟨U, hU⟩ := hn
  apply hU
  exact (H.original_action a ha i U).trans
    (YM.Integration.FullQLocal.ZeroRows.unmasked_zero
      (H.atom a i) hzero (a.packet.labels i).site U)

/-- Transfer the unchanged canonical-atom derivative estimate to the original
row support. Its nonnegative price is unchanged, including on zero rows. -/
theorem ZeroAwareVacuumPackets.regular_bounds
    (H : ZeroAwareVacuumPackets layers p rankCap width budget)
    (a : Piece G n) (ha : a ∈ layers) (i : ℕ) (c : ℝ)
    (hregular : p.Regular ((H.atom a i).footprint (a.packet.labels i).site)
      (fun U => (H.atom a i).unmasked U (a.packet.labels i).site))
    (hbound : p.supBounds (a.packet.labels i).site
      ((H.atom a i).footprint (a.packet.labels i).site)
      (fun U => (H.atom a i).unmasked U (a.packet.labels i).site) c) :
    p.Regular (a.packet.labels i).support (a.packet.action i) ∧
      p.supBounds (a.packet.labels i).site (a.packet.labels i).support
        (a.packet.action i) c := by
  have hrow : a.packet.action i =
      fun U => (H.atom a i).unmasked U (a.packet.labels i).site :=
    funext (H.original_action a ha i)
  rw [hrow]
  exact YM.Integration.FullQLocal.ZeroRows.regular_bounds_of_nonzero_support
    (H.atom a i) p (a.packet.labels i).site (a.packet.labels i).support c
    hregular hbound (H.support a ha i)

/-- The original masked row stays exactly zero; its support and label stay put. -/
theorem ZeroAwareVacuumPackets.masked_zero
    (H : ZeroAwareVacuumPackets layers p rankCap width budget)
    (a : Piece G n) (ha : a ∈ layers) (i : ℕ)
    (hzero : (H.atom a i).magnitude = 0) :
    masked p.threshold (a.packet.labels i).support (a.packet.action i) = 0 := by
  have hrow : a.packet.action i =
      fun U => (H.atom a i).unmasked U (a.packet.labels i).site :=
    funext (H.original_action a ha i)
  rw [hrow]
  exact YM.Integration.FullQLocal.ZeroRows.masked_zero
    (H.atom a i) hzero p.threshold (a.packet.labels i).site
    (a.packet.labels i).support

/-- The same original cover bill is paid by one quarter of the given path
width. All signs come from BudgetPoint; no new numerical hypothesis is used. -/
theorem ZeroAwareVacuumPackets.mass_budget
    (H : ZeroAwareVacuumPackets layers p rankCap width budget)
    (a : Piece G n) (ha : a ∈ layers) (i : ℕ) :
    p.mass (a.packet.labels i).support (H.atom a i).magnitude ≤
      Real.exp (p.supportExponent * H.coverOffset) *
        (H.atom a i).budget (width / 4) := by
  apply YM.Integration.FullQLocal.ZeroRows.mass_budget_of_nonzero_cover
    (H.atom a i) p (a.packet.labels i).support (width / 4)
    (H.coverOffset : ℝ)
  intro hne
  have hB : (0 : ℝ) < p.B := by exact_mod_cast p.B_pos
  have hreserve :
      p.supportExponent * (H.coverSlope : ℝ) ≤ (width / 4) * (p.B : ℝ) :=
    (div_le_iff₀ hB).mp H.width_reserved
  apply (mul_le_mul_iff_right₀ hB).mp
  calc
    (p.B : ℝ) *
        (p.supportExponent * (coverNumber p.B (a.packet.labels i).support : ℝ)) =
        p.supportExponent *
          ((p.B : ℝ) * (coverNumber p.B (a.packet.labels i).support : ℝ)) := by ring
    _ ≤ p.supportExponent *
        ((H.coverOffset : ℝ) * p.B +
          (H.coverSlope : ℝ) * (H.atom a i).length) :=
      mul_le_mul_of_nonneg_left (H.cover a ha i hne) p.exponent_pos.le
    _ = (p.B : ℝ) * (p.supportExponent * H.coverOffset) +
        (p.supportExponent * H.coverSlope) * (H.atom a i).length := by ring
    _ ≤ (p.B : ℝ) * (p.supportExponent * H.coverOffset) +
        ((width / 4) * p.B) * (H.atom a i).length :=
      add_le_add_right
        (mul_le_mul_of_nonneg_right hreserve (Nat.cast_nonneg _)) _
    _ = (p.B : ℝ) *
        (p.supportExponent * H.coverOffset +
          (width / 4) * (H.atom a i).length) := by ring

end YM.Integration.LocalComparison.Global
end
