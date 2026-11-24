import YM.Integration.ActualOriginalQFrozenInput

/-! Fixed finite layout data for the original-Q source, chosen before the
fee coefficient orders, regulator cutoff, physical period, and test values.
No numerical admission bound is inferred from these exact identities. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalQLayout
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison
open ActualOriginalQReaders
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {B : MS.Local.Physical.Deck G}
    {V : Type} [DecidableEq V] [Fintype V] (u : V → MS.Rake.Label B)

/-- The exact native finite-row maximum; the row list is unchanged. -/
def rankCap : ℕ :=
  let e := (Fintype.equivFin (ActualOriginalQPackets.Row (R := R) u)).symm
  Finset.univ.sup (fun k =>
    ActualRunKernelPackets.tokenRank R (ActualOriginalQPackets.degree u) (e k))

/-- One cutoff for every original SectionData column in the finite Glyph list. -/
def referenceLevel : ℕ :=
  (Finset.univ : Finset (Slot u)).sup (fun s => R.family.ref s.2.size)

omit [DecidableEq V] in
theorem reference_le {L : ℕ} (hL : referenceLevel R u ≤ L) (s : Slot u) :
    R.family.ref s.2.size ≤ L :=
  (Finset.le_sup (f := fun t : Slot u => R.family.ref t.2.size)
    (Finset.mem_univ s)).trans hL

variable {R} {p L n : ℕ} {hn : n ≤ L}
    (Q : MS.Land.Prescription B)
    (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
    (μ : ℝ) (orders : V → ℕ)

/-- Freezing changes no rank and the exact cap has no fee/cutoff dependence. -/
theorem rank_cap (N : ℕ) :
    (ActualOriginalQFrozenInput.packets Q D u μ orders N).rankCap = rankCap R u := rfl

/-- The whole frozen family has no explicit packet coupling power. -/
theorem power_cap (N : ℕ) :
    (ActualOriginalQFrozenInput.packets Q D u μ orders N).powerCap = 0 := rfl

end YM.Integration.ActualOriginalQLayout
end
