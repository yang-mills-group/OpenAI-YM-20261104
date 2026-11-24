import YM.OPE.Orbits.Kernel
import YM.OPE.Columns.SectorCost
import YM.RG12.Canonical.Low
import YM.RG12.Canonical.FromFrames
import YM.Pert.FirstTarget

/-!
# Data map on the physical side AFTER regulators at fixed m

Fin columns in full (possibly redundant in the physical quotient) master
chart, or in the reporting frame. Both denote ACTUAL labels on the same S.
No new ansatz for fields. Shifts/conversion of coordinates must be inserted
by the caller. The readout's elementary scale assumptions are MUCH less than
needed to produce reports at these scales. Passing from estimates on reporting
geometry only to those on arbitrary lengths will have to check the availability
of such a measuring frame there too. We specify the full-radius version here.

Keep both refinement limits and what may be read along any further limit.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter Spec Extraction Table OPE OPE.Orbits
open RG12
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G:Gauge}

abbrev home : Filter ℝ := 𝓝[>] (0:ℝ)
lemma ageLarge : Tendsto OPE.run home atTop := OPE.run_towards (r:=id) (h:=tendsto_id)
lemma lengthRate : RateIs home OPE.run (fun x=>x) (-1) := OPE.loglife (r:=id) tendsto_id
lemma positiveLength : ∀ᶠ r in home, 0 < r := lengthRate.pos

/-- On the reporting tail. This does not imply that such m exist for the
geometries/stencils and the post-L bounds of qfull; the caller still has
to check those for these measurements. -/
structure Reach (C:Family G) (level:ℝ→ℕ) : Prop where
    growing : Tendsto level home atTop
    nearby : Tendsto (fun r=> C.S.scale (level r) / OPE.run r) home (𝓝 1)

abbrev Free (C:Family G) (d:ℕ):= (Maxwell.freeTable C.labels).Field d
abbrev Slot (C:Family G) (d:ℕ):= C.label d ⊕ Free C d
variable {C : Family G} {f:Extraction.Order}{S:Table C.book}

/-- L must use F's field extraction. The coupling-coordinate chart,
including any change from threshold-coordinates at either set of slots,
is NOT assumed to be literally the identity. Only the horizon-zero unit
is assumed preserved without converting. The alternative of using some
more general linear map for capture (enlarging the letter space, for
example by address indices) is not implemented here. Equality of `master`
with the readout in the overlap computations must be proved by producers. -/
structure Layout (F:Final C f S) where
    level : ℝ → ℕ
    charts : ∀ d:ℕ, ℕ → RepChart C d
    lens : Filter UVIndex
    notbot : lens.NeBot
    certified : lens ≤ f.fuse
    observes : Observing C F.room.cutoff lens charts
    shift : ∀ d:ℕ, ℝ → C.label d ≃ₗ[ℂ] C.label d
    frame : ∀ d:ℕ, ℝ → Free C d ≃ₗ[ℂ] S.Field d

variable {F : Final C f S} (L:Layout F)

/-- Full V_h readout map, before expressing in independent frame.
Charts are limits at fixed level. -/
def master (d:ℕ)(r:ℝ): C.label d→ₗ[ℂ] S.Field d :=
    (engineering L.charts d (L.level r)).comp (L.shift d r).toLinearMap

def input (r:ℝ) (d:ℕ) : Slot C d → S.Field d :=
    Sum.elim (master L d r) (L.frame d r)

/-- Measurement assumptions for this consumer; NOT presently supplied.
`built` is a (spatial-power scale) price on reporting frame fields on
this same alphabet; they needn't be single-height. Real and rotation
alignment, the stronger prices for diagram readout and the actual
normalization prescription are separate obligations. -/
structure Located : Prop where
    level : Reach C L.level
    unit₀ : ∀ᶠ r in home,L.shift 0 r (C.labels.level 0).e0=(C.labels.level 0).e0
    unit d : ∀ᶠ r in home,L.frame d r ((Maxwell.freeTable C.labels).unit d)= S.unit d
    nested {d e : ℕ} (he:d ≤ e) : ∀ᶠ r in home,∀ v,
      L.frame e r ((Maxwell.Free.scheme C.labels).rise he v)= F.sector.derivatives.rise he (L.frame d r v)
    rebased d : RateLE home OPE.run (fun r=> (L.shift d r).toContinuousLinearEquiv.toContinuousLinearMap) 0
    built (d:ℕ) (v:Free C d) : ∃ p : (j:Fin (d+1))→ℝ→C.label j,
      (∀ j, RateLE home OPE.run (p j) 0) ∧
      ∀ᶠ r in home,L.frame d r v = ∑ j : Fin (d+1),F.sector.derivatives.rise
        (Nat.le_of_lt_succ j.isLt) (master L j.val r (p j r))

end YM.RG17
