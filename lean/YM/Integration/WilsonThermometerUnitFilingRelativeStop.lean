import YM.Integration.WilsonThermometerUnitFilingRelative
import YM.Integration.WilsonThermometerUnitFilingWhole

/-! Fixed-date reading of a signed priced numerator. Raw integral linearity is applied
only after integrability on the same original Haar fibre. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingRelativeStop
open Function Filter Set MeasureTheory Finset Lattice Wilson Labels RG Source Extra.Histories
open Push Marker PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent FVA1
open OriginalForcedAddresses RG12 RG16 RG16.Literal Trace.Physical.GermGraph
open OPE.Cards Primitives.GCC.Anchor Climb WilsonPositionThermometerCapStation
open WilsonThermometerCourseIntake WilsonThermometerUnitFilingCylinder WilsonThermometerUnitFilingFeed
open WilsonThermometerCenteredAlgebra WilsonThermometerAlignedCells
open XSpace XSpace.Rose Cells Push.GridApprox WilsonThermometerWeightedCapture
open private sum_triples from YM.Integration.WilsonThermometerAlignedCells
open private admitted from YM.Integration.WilsonThermometerUnitFilingDeposit
open scoped BigOperators Topology Classical
open MeasureTheory WilsonThermometerUnitFilingCoarse

variable {G:Gauge} (R:Run G) (simple:G.Simple) {N per b u:ℕ} (live:b≤N) (older:u≤b)
  (Y:Cut R.family N per) (cont:Continuous Y)
local notation "ear" => credit R.family N per 0 Y b live

include simple cont in
theorem original (model:Config G (R.family.side b per)→ℂ) (raw:Integrable (ear-model) (prior G _))
    {E:ℝ} (tested:‖reading R (N:=N) (ear-model) u older‖≤E)
    (door:Opened R.family 0 u per) (book:Booked R.family N per 0 Y u (older.trans live)):
    ‖report R Y u-reading R (N:=N) model u older‖≤E:=by
  have ht:=WilsonThermometerUnitFilingInvoice.credit_live R live Y cont
  have hm:Integrable model (prior G _):=by
    have same:ear-(ear-model)=model:=sub_sub_cancel _ _
    rw [←same];exact ht.sub raw
  have signed:=WilsonThermometerUnitFilingRaw.add R (N:=N) (ear-model) model raw hm older
  rw [sub_add_cancel] at signed
  have filed:report R Y u=reading R (N:=N) ear u older:=by
    rw [WilsonThermometerUnitFilingCourse.filed R simple Y door (older.trans live) book]
    unfold reading
    rw [WilsonThermometerUnitFilingCoarse.cutoff R live older Y cont]
  rw [filed,signed,add_sub_cancel_right];exact tested

end YM.Integration.WilsonThermometerUnitFilingRelativeStop
