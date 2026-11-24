import YM.Integration.WilsonPositionScaleLawFixed

/-! The inverse of the actual position frame on fixed physical names commutes
with each predetermined grade inclusion. Contributions above the physical
horizon vanish exactly and all remaining projectors agree at every horizon. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawInclusion
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize PhysicalNext.Repeat.Legato FVA2 FVA2.Register FVA2.Scale
open WilsonPositionScaleLawHome (positioned)
open WilsonPositionScaleLawGrade (grade reads)
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)(V:Store G)

private theorem upward (C:Family G){j d:ℕ}(hj:j≤d)(x:(Bel C.book).Field j):
    fields C.labels d ((scheme C.labels).rise hj x)=up hj (fields C.labels j x):=
  Subtype.ext (address_rise C.labels d hj x)


theorem inverse (lead:Leading F J){j d:ℕ}(hj:j≤d):∀ᶠr in trail,∀O:S.Field j,
    (positioned F J V r d).symm (F.sector.derivatives.rise hj O)=
      (scheme C.labels).rise hj ((positioned F J V r j).symm O):=by
  filter_upwards [WilsonPositionScaleLawNative.raised F J V lead hj] with r eq O
  apply (positioned F J V r d).injective
  rw [LinearEquiv.apply_symm_apply,eq,LinearEquiv.apply_symm_apply]


def row (d:ℕ)(i:Fin (d+1))(r:ℝ)(O:S.Field d):=(grade C i) ((positioned F J V r d).symm O)

theorem shared (lead:Leading F J){j d:ℕ}(hj:j≤d)(i:Fin (j+1)):∀ᶠr in trail,∀O:S.Field j,
    row F J V d ⟨i.val,by omega⟩ r (F.sector.derivatives.rise hj O)=
      (scheme C.labels).rise hj (row F J V j i r O):=by
  filter_upwards [inverse F J V lead hj] with r eq O
  apply (fields C.labels d).injective
  dsimp only [row]
  rw [eq,reads,upward,upward,reads]
  rfl

theorem upper (lead:Leading F J){j d:ℕ}(hj:j≤d)(i:Fin (d+1))(hi:j < i.val):∀ᶠr in trail,∀O:S.Field j,
    row F J V d i r (F.sector.derivatives.rise hj O)=0:=by
  filter_upwards [inverse F J V lead hj] with r eq O
  apply (fields C.labels d).injective
  dsimp only [row]
  rw [eq,reads,upward,map_zero]
  change en (Level.within i) (part d i.val (up hj _))=0
  rw [part_up,part_zero hi,map_zero]

end YM.Integration.WilsonPositionScaleLawInclusion
end
