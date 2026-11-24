import YM.Integration.ActualStartupGradedInput
import YM.Integration.QLocalVacuumDerivativePrice

/-!
# Invoices for the original retained startup album

The structural proof is the corresponding part of the native Patch.leaf
argument. Its flat-Hessian conclusion is used only at the actual ranks
5+j. Numerical credits use the canonical Wages price at each original
rank, with its own threshold power and original exponential row budget.

Repricing changes only Piece.credit. Every original packet, padded row,
support, coupling power and curvature rank is retained. This does not
bound an arbitrary old credit or pay the rank-two kinetic component.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualStartupInvoice

open Function Finset Lattice Wilson RG
open WilsonStartup WilsonStartup.Start WilsonStartup.IterationFour
open Padded Quad Work Tensor Next.Fluctuations
open YM.IterationFour.Vacuum
open ActualStartupVacuumPackets ActualStartupGradedInput
open LocalComparison.Global
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff

attribute [local instance] Gauge.frobInner

variable {G : Gauge} {n : Side} {p : BudgetPoint}

/-- Native structural slate obligations, with the numerical credit supplied
separately. The vanishing statement genuinely requires rank greater than two. -/
theorem slate_invoice_of_credit {f : G.Mat → ℝ} {q : ℕ}
    (h : Stamp (G := G) f q) (hq : 2 < q) (u : ℝ) {c : ℝ}
    (hc : ∃ v : ℕ → ℝ,
      (∀ i, p.supBounds ((slate G n u f).labels i).site
        ((slate G n u f).labels i).support ((slate G n u f).action i) (v i)) ∧
      ∀ o, SumBudget (fun i => if ((slate G n u f).labels i).site = o then
        p.mass ((slate G n u f).labels i).support (v i) else 0) c) :
    (slate G n u f).Invoice p c := by
  let B := slate G n u f
  have hv : ∀ i, p.Regular (B.labels i).support (B.action i) ∧
      B.action i 1 = 0 ∧ (∀ x y, logHessian (B.action i) x y = 0) := by
    intro i
    unfold B slate
    dsimp only
    split
    next hn =>
      dsimp only [Function.comp_apply]
      cases name (Sheet n) i with
      | inl a =>
          change p.Regular a.skin _ ∧ (u • element G f a.positive) _ = 0 ∧
            (∀ x y, logHessian (u • element G f a.positive) x y = 0)
          have hf := h.flat a.positive
          let g := element G f a.positive
          rw [a.skin_positive]
          refine ⟨Start.times_reg u (h.regular ..), ?_, fun x y => ?_⟩
          · have hz := congrArg (Tensor.diagonal · (0 : Directions G n))
              (hf 0 (by omega))
            have hg : g 1 = 0 := by
              simpa [Tensor.diagonal, Function.comp_def, g, G07.at_zero_increment]
                using hz
            change u * g 1 = 0
            rw [hg, mul_zero]
          change iteratedFDeriv ℝ 2 (u • (g ∘ increment 1)) 0 ![x, y] = 0
          rw [iteratedFDeriv_const_smul_apply
            ((h.smooth ..).contDiffAt.of_le le_top),
            show iteratedFDeriv ℝ 2 (g ∘ increment 1) 0 = 0 from hf 2 hq,
            smul_zero]
          rfl
      | inr a =>
          change p.Regular _ 0 ∧ 0 = 0 ∧ (∀ x y, logHessian 0 x y = 0)
          exact ⟨Start.zero_reg, rfl, fun x y => by simp [logHessian]⟩
    exact ⟨Start.zero_reg, rfl, fun x y => by simp [logHessian]⟩
  refine ⟨fun i => (hv i).1, fun i => (hv i).2.1,
    fun i _ x y _ _ => (hv i).2.2 x y, ?_, hc⟩
  intro s b
  refine ⟨sends (sheetAction s b), fun i => ?_⟩
  unfold slate
  dsimp only [Function.comp_apply]
  simp_rw [name_sends, eInfo_transport, fixed_sends]
  refine ⟨trivial, trivial, fun U => ?_⟩
  split
  next hi =>
    cases name (Sheet n) i with
    | inl a =>
        change u * element G f (Key.perm s b a).positive U =
          u * element G f a.positive (pull s b U)
        have he (a : Key n) (U : Config G n) :
            element G f a.positive U = element G f a.root (a.frame U) :=
          h.turns ..
        rw [he, Key.oriented, he a (pull s b U)]
        rfl
    | inr a => rfl
  rfl

/-- The exact per-rank credit; in particular threshold^rank is not replaced
by a maximum over smaller ranks. -/
def pieceDerivativeCost (G : Gauge) (p : BudgetPoint) (S : Stage)
    (width : ℝ) (rank : ℕ) : ℝ :=
  (Next.Scheduling.Wages.startup G rank p.power p.order * p.threshold ^ rank *
    Extra.Iteration.momentPrice (Next.Scheduling.Wages.grade rank p.power p.order)
      (3 * width / 4) *
    Real.exp (p.supportExponent * (5 ^ 4 : ℕ))) *
  layerCost G (Start.weight S.clip 1) width rank

/-- Every retained original row has rank 5+j; kinetic rank-two rows are absent. -/
theorem retained_rank (G : Gauge) (n : Side) (p : BudgetPoint)
    (S : Stage) (r : ℕ) (a : Piece G n) (ha : a ∈ album G n p S r) :
    5 ≤ a.rank ∧ a.rank = a.power + 2 := by
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
  change 5 ≤ 5 + j ∧ 5 + j = (3 + j) + 2
  omega

/-- An actual Invoice, with flatness/nullity/movement proved from the native
slate and a genuine Wages credit for the same complete original packet. -/
theorem piece_invoice (G : Gauge) (n : Side) (p : BudgetPoint)
    (S : Stage) (r : ℕ) (width : ℝ) (hw : 0 < width)
    (a : Piece G n) (ha : a ∈ album G n p S r) :
    a.packet.Invoice p (pieceDerivativeCost G p S width a.rank) := by
  let H := (gradedAlbum G n p S r width hw.le).packets
  have hc : ∃ v : ℕ → ℝ,
      (∀ i, p.supBounds (a.packet.labels i).site (a.packet.labels i).support
        (a.packet.action i) (v i)) ∧
      ∀ o, SumBudget (fun i => if (a.packet.labels i).site = o then
        p.mass (a.packet.labels i).support (v i) else 0)
        (pieceDerivativeCost G p S width a.rank) := by
    refine ⟨fun i => Next.Scheduling.Wages.price p (H.atom a i),
      fun i => H.canonical_price a ha i, fun o => ?_⟩
    exact H.derivative_budget hw a ha o
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
  exact slate_invoice_of_credit (terms_stamp G (5 + j)) (by omega)
    (Start.weight S.clip 1) hc

/-- Bookkeeping only: every field except the numerical credit is literal. -/
def reprice (credit : Piece G n → ℝ) (a : Piece G n) : Piece G n :=
  { a with credit := credit a }

def repriceLayers (credit : Piece G n → ℝ) (L : List (Piece G n)) :=
  L.map (reprice credit)

theorem reprice_data (credit : Piece G n → ℝ) (L : List (Piece G n)) :
    (repriceLayers credit L).map (fun a => (a.power, a.rank, a.packet)) =
      L.map (fun a => (a.power, a.rank, a.packet)) := by
  simp only [repriceLayers, List.map_map, Function.comp_def, reprice]

theorem reprice_renders (credit : Piece G n → ℝ) (L : List (Piece G n))
    (g : ℝ) (p : BudgetPoint) (U : Config G n) :
    Render.renders (Render.prefactor g) p U (repriceLayers credit L) =
      Render.renders (Render.prefactor g) p U L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      change Render.prefactor g a * a.packet.amount p U +
          Render.renders (Render.prefactor g) p U (repriceLayers credit L) =
        Render.prefactor g a * a.packet.amount p U +
          Render.renders (Render.prefactor g) p U L
      rw [ih]

theorem reprice_adorn (credit : Piece G n → ℝ) (L : List (Piece G n))
    (g : ℝ) (A : Activities G n) :
    Render.adorn (Render.prefactor g) A (repriceLayers credit L) =
      Render.adorn (Render.prefactor g) A L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      change a.packet.attach (Render.prefactor g a)
          (Render.adorn (Render.prefactor g) A (repriceLayers credit L)) =
        a.packet.attach (Render.prefactor g a)
          (Render.adorn (Render.prefactor g) A L)
      rw [ih]

theorem reprice_unmasked (credit : Piece G n → ℝ) (L : List (Piece G n))
    (g : ℝ) (U : Config G n) :
    unmaskedLayers (repriceLayers credit L) g U = unmaskedLayers L g U := by
  simp only [unmaskedLayers, repriceLayers, List.map_map, Function.comp_def,
    reprice, Render.prefactor, Render.stepOrder]

/-- The actual new credit is paid on the same list, with duplicate occurrences
and zero rows still present. -/
def paidAlbum (G : Gauge) (n : Side) (p : BudgetPoint) (S : Stage)
    (r : ℕ) (width : ℝ) : List (Piece G n) :=
  repriceLayers (fun a => pieceDerivativeCost G p S width a.rank)
    (album G n p S r)

theorem paid_permits (G : Gauge) (n : Side) (p : BudgetPoint)
    (S : Stage) (r : ℕ) (width : ℝ) (hw : 0 < width) :
    Render.permits (paidAlbum G n p S r width) p := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  exact piece_invoice G n p S r width hw a ha

/-- The same zero-aware atom/geometry budget survives the credit-only change. -/
def paidPackets (G : Gauge) (n : Side) (p : BudgetPoint) (S : Stage)
    (r : ℕ) (width : ℝ) (hw : 0 ≤ width) :
    ZeroAwareVacuumPackets (paidAlbum G n p S r width) p (r + 2) width
      (albumCost G p S r width) where
  atom a := rowAtom G n (Start.weight S.clip 1) a.rank
  rank_bounded b hb := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact (albumPackets G n p S r width hw).rank_bounded a ha
  invariant b _ i := rowAtom_invariant (Start.weight S.clip 1) b.rank i
  original_action b hb i U := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact (albumPackets G n p S r width hw).original_action a ha i U
  support b hb i hne := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact (albumPackets G n p S r width hw).support a ha i hne
  pieceCost a := layerCost G (Start.weight S.clip 1) width a.rank
  piece_cost_nonnegative a _ :=
    layerCost_nonnegative (Start.weight S.clip 1) width a.rank
  exponential b hb o := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact (albumPackets G n p S r width hw).exponential a ha o
  total := by
    simpa only [paidAlbum, repriceLayers, List.map_map, Function.comp_def,
      reprice, albumPackets] using (albumPackets G n p S r width hw).total
  coverOffset := 5 ^ 4
  coverSlope := 0
  cover b hb i hne := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact (albumPackets G n p S r width hw).cover a ha i hne
  width_reserved := (albumPackets G n p S r width hw).width_reserved
  cover_cost := (albumPackets G n p S r width hw).cover_cost

/-- No new atoms, ranks, powers, width or exponential budget are introduced. -/
def paidGradedAlbum (G : Gauge) (n : Side) (p : BudgetPoint) (S : Stage)
    (r : ℕ) (width : ℝ) (hw : 0 ≤ width) :
    FullQLocal.GradedVacuumLayers (paidAlbum G n p S r width) p r (r + 2)
      width (albumCost G p S r width) where
  packets := paidPackets G n p S r width hw
  orders b hb := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact (gradedAlbum G n p S r width hw).orders a ha
  leading_rank b hb := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact (gradedAlbum G n p S r width hw).leading_rank a ha

/-- The original fine album may use a different BudgetPoint. Its packet
does not depend on that old credit, so the requested norm pays the same row. -/
theorem piece_invoice_at (G : Gauge) (n : Side)
    (original requested : BudgetPoint) (S : Stage) (r : ℕ)
    (width : ℝ) (hw : 0 < width)
    (a : Piece G n) (ha : a ∈ album G n original S r) :
    a.packet.Invoice requested
      (pieceDerivativeCost G requested S width a.rank) := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
  exact piece_invoice G n requested S r width hw
    (top_terms G n requested S j) (List.mem_map.mpr ⟨j, hj, rfl⟩)

/-- The requested-norm paid album is exactly a credit-only repricing of
the original fine album. No threshold, derivative order or old credit is
silently transported between the two BudgetPoints. -/
theorem paid_from_original (G : Gauge) (n : Side)
    (original requested : BudgetPoint) (S : Stage) (r : ℕ) (width : ℝ) :
    paidAlbum G n requested S r width =
      repriceLayers (fun a : Piece G n =>
        pieceDerivativeCost G requested S width a.rank)
        (album G n original S r) := by
  simp only [paidAlbum, repriceLayers, album, List.map_map, Function.comp_def,
    reprice, top_terms]

end YM.Integration.ActualStartupInvoice
end
