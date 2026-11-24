import YM.Integration.QLocalVacuumRowRegularity
import YM.Next.SCHEDULE.TensorCost

/-!
# Actual derivative prices from the original exponential atom budget

Use the native ordered-left derivative bound on each unchanged atom. One
quarter of the given width pays the original support cover; the remaining
three quarters pay the polynomial length moment. All original layer
occurrences, including duplicates and zero rows, are retained.

These are consequences of the supplied atom/geometry receipt. They do not
prove the qlocal estimate, flatness, affine-nullity, row permutation laws,
or the match to a pre-existing Piece.credit.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison.Global

open Lattice Wilson RG
open IterationFour.Vacuum
open Extra.Iteration
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {layers : List (Piece G n)}
    {p : BudgetPoint} {rankCap : ℕ} {width budget : ℝ}

/-- All ordered-left derivatives use the native price of the unchanged atom. -/
theorem ZeroAwareVacuumPackets.canonical_price
    (H : ZeroAwareVacuumPackets layers p rankCap width budget)
    (a : Piece G n) (ha : a ∈ layers) (i : ℕ) :
    p.supBounds (a.packet.labels i).site (a.packet.labels i).support
      (a.packet.action i) (Next.Scheduling.Wages.price p (H.atom a i)) :=
  H.canonical_bound a ha i _
    (Next.Scheduling.Wages.total p (H.atom a i) (a.packet.labels i).site)

/-- A finite-rank derivative cost independent of the number of rows or the volume. -/
def ZeroAwareVacuumPackets.derivativeFactor
    (H : ZeroAwareVacuumPackets layers p rankCap width budget) (k : ℕ) : ℝ :=
  Next.Scheduling.Wages.startup G k p.power p.order * p.threshold ^ k *
    momentPrice (Next.Scheduling.Wages.grade k p.power p.order) (3 * width / 4) *
      Real.exp (p.supportExponent * H.coverOffset)

private theorem factor_nonnegative
    (H : ZeroAwareVacuumPackets layers p rankCap width budget)
    (hw : 0 < width) (k : ℕ) : 0 ≤ H.derivativeFactor k := by
  have hs : 0 ≤ Next.Scheduling.Wages.slotCost G p.power p.order 0 :=
    zero_le_one.trans (Next.Scheduling.Wages.slot_ge G p.power p.order 0)
  have ht := p.threshold_pos
  have hm := (momentPrice_pos (Next.Scheduling.Wages.grade k p.power p.order)
    (show 0 < 3 * width / 4 by positivity)).le
  unfold ZeroAwareVacuumPackets.derivativeFactor Next.Scheduling.Wages.startup
  positivity

private theorem moment_absorb {k : ℕ} (a : Atom G k)
    (hw : 0 < width) (d : ℕ) :
    ((a.length : ℝ) + 1) ^ d * a.budget (width / 4) ≤
      momentPrice d (3 * width / 4) * a.budget width := by
  have hz : 0 ≤ (a.length : ℝ) := by positivity
  have hp := spendMoment d (show 0 < 3 * width / 4 by positivity) hz
  have hb : 0 ≤ a.budget (width / 4) := by
    unfold Atom.budget Atom.magnitude
    positivity
  calc
    _ ≤ (momentPrice d (3 * width / 4) *
        Real.exp ((3 * width / 4) * a.length)) * a.budget (width / 4) := by
      exact mul_le_mul_of_nonneg_right (by simpa only [add_comm] using hp) hb
    _ = momentPrice d (3 * width / 4) * a.budget width := by
      unfold Atom.budget
      calc
        _ = momentPrice d (3 * width / 4) * a.magnitude *
            (Real.exp ((3 * width / 4) * a.length) *
             Real.exp ((width / 4) * a.length)) := by ring
        _ = _ := by
          rw [← Real.exp_add]
          rw [show (3 * width / 4) * (a.length : ℝ) +
              (width / 4) * a.length = width * a.length by ring]
          ring

/-- The actual original-support derivative mass is paid at the full given width. -/
theorem ZeroAwareVacuumPackets.derivative_row_le
    (H : ZeroAwareVacuumPackets layers p rankCap width budget)
    (hw : 0 < width) (a : Piece G n) (ha : a ∈ layers) (i : ℕ) :
    p.mass (a.packet.labels i).support (Next.Scheduling.Wages.price p (H.atom a i)) ≤
      H.derivativeFactor a.rank * (H.atom a i).budget width := by
  let t := Next.Scheduling.Wages.startup G a.rank p.power p.order * p.threshold ^ a.rank
  let d := Next.Scheduling.Wages.grade a.rank p.power p.order
  have hs : 0 ≤ Next.Scheduling.Wages.slotCost G p.power p.order 0 :=
    zero_le_one.trans (Next.Scheduling.Wages.slot_ge G p.power p.order 0)
  have ht : 0 ≤ t := by
    have hp := p.threshold_pos
    unfold t Next.Scheduling.Wages.startup
    positivity
  have hl : 0 ≤ ((H.atom a i).length : ℝ) + 1 := by positivity
  have hc : 0 ≤ Real.exp (p.supportExponent * H.coverOffset) := (Real.exp_pos _).le
  calc
    _ = t * ((((H.atom a i).length : ℝ) + 1) ^ d *
        p.mass (a.packet.labels i).support (H.atom a i).magnitude) := by
      rw [Next.Scheduling.Wages.scan]
      unfold t d BudgetPoint.mass
      ring
    _ ≤ t * ((((H.atom a i).length : ℝ) + 1) ^ d *
        (Real.exp (p.supportExponent * H.coverOffset) *
          (H.atom a i).budget (width / 4))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (H.mass_budget a ha i) (pow_nonneg hl d)) ht
    _ = (t * Real.exp (p.supportExponent * H.coverOffset)) *
        ((((H.atom a i).length : ℝ) + 1) ^ d * (H.atom a i).budget (width / 4)) := by ring
    _ ≤ (t * Real.exp (p.supportExponent * H.coverOffset)) *
        (momentPrice d (3 * width / 4) * (H.atom a i).budget width) :=
      mul_le_mul_of_nonneg_left (moment_absorb (H.atom a i) hw d) (mul_nonneg ht hc)
    _ = H.derivativeFactor a.rank * (H.atom a i).budget width := by
      unfold ZeroAwareVacuumPackets.derivativeFactor t d
      ring

/-- Per-root summability retains the original labels and support weights. -/
theorem ZeroAwareVacuumPackets.derivative_budget
    (H : ZeroAwareVacuumPackets layers p rankCap width budget)
    (hw : 0 < width) (a : Piece G n) (ha : a ∈ layers) (o : Site n) :
    SumBudget (fun i : ℕ => if (a.packet.labels i).site = o then
      p.mass (a.packet.labels i).support (Next.Scheduling.Wages.price p (H.atom a i))
      else 0) (H.derivativeFactor a.rank * H.pieceCost a) := by
  apply Cost.mono (Cost.scale (H.exponential a ha o)
    (H.derivativeFactor a.rank) (factor_nonnegative H hw a.rank))
  · intro i
    split
    · exact mul_nonneg (Real.exp_pos _).le
        (Next.Scheduling.Wages.total p (H.atom a i) (a.packet.labels i).site).1
    · exact le_rfl
  intro i
  by_cases hi : (a.packet.labels i).site = o
  · simp only [hi, if_true]
    exact H.derivative_row_le hw a ha i
  · simp only [hi, if_false, mul_zero]
    exact le_rfl

/-- A finite cap using only the requested rank capacity. -/
def ZeroAwareVacuumPackets.derivativeCap
    (H : ZeroAwareVacuumPackets layers p rankCap width budget) : ℝ :=
  ∑ k ∈ Finset.range (rankCap + 1), H.derivativeFactor k

private theorem cap_nonnegative
    (H : ZeroAwareVacuumPackets layers p rankCap width budget)
    (hw : 0 < width) : 0 ≤ H.derivativeCap :=
  Finset.sum_nonneg (fun k _ => factor_nonnegative H hw k)

private theorem factor_le_cap
    (H : ZeroAwareVacuumPackets layers p rankCap width budget)
    (hw : 0 < width) (a : Piece G n) (ha : a ∈ layers) :
    H.derivativeFactor a.rank ≤ H.derivativeCap := by
  exact Finset.single_le_sum (fun k _ => factor_nonnegative H hw k)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le (H.rank_bounded a ha)))

/-- The full list, with duplicate layer occurrences counted, has no volume loss. -/
theorem ZeroAwareVacuumPackets.full_derivative_budget
    (H : ZeroAwareVacuumPackets layers p rankCap width budget)
    (hw : 0 < width) (o : Site n) :
    SumBudget (fun i : ℕ => (layers.map (fun a => if (a.packet.labels i).site = o then
      p.mass (a.packet.labels i).support (Next.Scheduling.Wages.price p (H.atom a i))
      else 0)).sum) (H.derivativeCap * budget) := by
  let row (a : Piece G n) (i : ℕ) := if (a.packet.labels i).site = o then
    p.mass (a.packet.labels i).support (Next.Scheduling.Wages.price p (H.atom a i)) else 0
  have hcap := cap_nonnegative H hw
  have hlist (L : List (Piece G n)) :
      (∀ a ∈ L, a ∈ layers) →
      SumBudget (fun i : ℕ => (L.map (fun a => row a i)).sum)
        (H.derivativeCap * (L.map H.pieceCost).sum) := by
    induction L with
    | nil =>
      intro _
      simpa only [List.map_nil, List.sum_nil, mul_zero] using
        (show SumBudget (fun _ : ℕ => (0 : ℝ)) 0 from
          ⟨fun _ => le_rfl, summable_zero, by simp⟩)
    | cons a L ih =>
      intro hL
      have ha : a ∈ layers := hL a (List.mem_cons_self)
      have htail := ih (fun b hb => hL b (List.mem_cons_of_mem a hb))
      have hhead : SumBudget (row a) (H.derivativeCap * H.pieceCost a) :=
        Cost.enlarge (H.derivative_budget hw a ha o)
          (mul_le_mul_of_nonneg_right (factor_le_cap H hw a ha)
            (H.piece_cost_nonnegative a ha))
      have hsum : SumBudget (fun i => row a i + (L.map (fun b => row b i)).sum)
          (H.derivativeCap * H.pieceCost a +
            H.derivativeCap * (L.map H.pieceCost).sum) := by
        refine ⟨fun i => add_nonneg (hhead.1 i) (htail.1 i),
          hhead.2.1.add htail.2.1, ?_⟩
        rw [Summable.tsum_add hhead.2.1 htail.2.1]
        exact add_le_add hhead.2.2 htail.2.2
      simpa only [List.map_cons, List.sum_cons, mul_add] using hsum
  exact Cost.enlarge (hlist layers (fun _ h => h))
    (mul_le_mul_of_nonneg_left H.total hcap)

end YM.Integration.LocalComparison.Global

end
