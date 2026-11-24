import YM.Integration.WilsonMatrixTicketLanesReportedCredit
import YM.Integration.WilsonInvariantActionMixedMaterial

/-! The nonlinear physical operator in the measured fresh block is exactly the unmasked primary, including the affine unit. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesConnectedRegistered
open Function MeasureTheory Lattice RG Wilson MergeProof Source Push.Local RG16.Literal
open WilsonInheritedRegisteredField WilsonMatrixTicketLanesReportedPivot
open private primary head from YM.Integration.WilsonMatrixTicketLanesReportedCredit
open scoped Classical BigOperators
variable {G:Gauge} (R:PhysicalNext.Repeat.Legato.Run G) {k N per d:ℕ}

/-- The zero label is kept as a separate constant. The mask applies only to this genuine nonlinear core. -/
def raw (live:k≤N) (v:R.family.label d) (o:Site (R.family.side k per)) : Config G (R.family.side k per) → ℂ :=
  let P:=R.family.path.rep N per k;let Z:=packet (C:=R.family) R.makes live v o;let S:=R.family.localSection d;let L:=R.family.labels.level d
  S.places (L.scaled P.p.threshold⁻¹ (L.core Z.x)) o

def maskError (live:k≤N) (v:R.family.label d) (o:Site (R.family.side k per)) (U:Config G (R.family.side k per)):ℂ:=
  let P:=R.family.path.rep N per k;let S:=R.family.localSection d;let A:=raw R live v o
  alto R.family.path k d*(masked P.p.threshold (S.footprint o) A U-A U)

/-- This is the very same pointwise compact observable which is integrated in the fresh positive block. -/
theorem unmasked (live:k≤N) (v:R.family.label d) (o:Site (R.family.side k per)) (U:Config G (R.family.side k per)):
    R.family.O k per (center R k N per v) o U = alto R.family.path k d*((packet (C:=R.family) R.makes live v o).x 0+raw R live v o U):=by
  rw [head R live o v U,primary R]
  rfl

theorem registered (live:k≤N) (v:R.family.label d) (o:Site (R.family.side k per)) (U:Config G (R.family.side k per)):
    regular (C:=R.family) R.makes live v o U=R.family.O k per (center R k N per v) o U+maskError R live v o U+
      alto R.family.path k d*∑' i,(packet (C:=R.family) R.makes live v o).maskedTerm (R.family.path.rep N per k) i U:=by
  rw [unmasked R live v o U]
  unfold regular Coefficient.exponentialEntry maskError raw
  dsimp only
  ring

/-- The signed full earlier cohort, including every registered term of the original effective action. -/
theorem four (live:k≤N) (v:R.family.label 4) (o:Site (R.family.side k per)) (U:Config G (R.family.side k per)):
    regular (C:=R.family) R.makes live v o U=R.family.O k per (center R k N per v) o U+maskError R live v o U+
      WilsonInvariantActionMixedMaterial.earlier (C:=R.family) R.makes live v o Set.univ U:=by
  simpa only [WilsonInvariantActionMixedMaterial.earlier,Set.mem_univ,if_true] using registered R live v o U

/-- Off the actual flagged footprint, the exact mask correction is zero on the group configuration itself. -/
theorem clean (live:k≤N) (v:R.family.label d) (o:Site (R.family.side k per)) (U:Config G (R.family.side k per))
    (good:Healthy (R.family.path.rep N per k).p.threshold ((R.family.localSection d).footprint o) U): maskError R live v o U=0:=by
  unfold maskError
  dsimp only
  rw [masked_eq _ _ _ _ good,sub_self,mul_zero]

theorem whole (live:k≤N) (v:R.family.label 4) (o:Site (R.family.side k per)) (U:Config G (R.family.side k per)):
    field (C:=R.family) R.makes live v o U=R.family.O k per (center R k N per v) o U+maskError R live v o U+
      WilsonInvariantActionMixedMaterial.earlier (C:=R.family) R.makes live v o Set.univ U+forced (C:=R.family) R.makes live v o U:=by
  rw [separated (C:=R.family) R.makes live v o U,four R live v o U]

end YM.Integration.WilsonMatrixTicketLanesConnectedRegistered
