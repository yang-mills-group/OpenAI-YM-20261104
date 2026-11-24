import YM.Integration.WilsonAddressedCorrectedAlignedFare
import YM.Integration.WilsonAddressedAlignedColumn
import YM.Integration.WilsonThermometerOffsetLedger

/-! The literal oriented cubic, for all its physical subproducts, on one enrolled original trajectory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedCorrectedAlignedSource
open Function Filter Set Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG RG12 Labels Extra.Histories RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local
open PhysicalNext.Repeat.Legato MergeProof Accent Trace.Physical Trace.Physical.GermGraph Work.G08 Next.Rank
open RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize XSpace.Rose
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerReading
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource WilsonPositionCorrectedCap
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open scoped BigOperators Classical Topology
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {T:Table R.family.book}
variable (F:Final R.family f T) (P:ℝ→tower T) (V:Store G) {H:(Bel R.family.book).Hierarchy}
variable {l:Ultrafilter (ℕ×ℕ)} (A:ℝ→WilsonPositionThermometerCapStation.Group R.family 6)

def filed (R:Run G) (Z:WilsonPositionThermometerCapStation.Group R.family 6) (k N p:ℕ) (hk:k≤N) (ε:ℝ):Prop:=
  ∃ (Q:Sight R.family 6 p) (r:Emblems R.family 6) (opened:Opened R.family 6 k p),
  Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) k N p 6 (digits R N p 0) Q r ∧
  ∀ s:Badge,let x:=Z.station.wheel.atCut (N,p) (index Z (grade 0)) (vector Z s 0)
  let y:=WilsonAddressedAlignedColumn.offer R x opened hk
  (R.family.S.a k:ℂ)^6 • (R.family.factory 6 N p).terminal (finer r hk y (primaryLetter 6))=x ∧
  size y ≤ 2*((R.family.S.a k/R.family.S.a Z.station.k) *
    ((R.family.path.levels.clock.hatBeta Z.station.k)^ε * WilsonThermometerMarchReference.fee R.family s 0))

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (paid:Book (f:=f) (l:=l) (H:=H) A P) (lead:Leading F P) (ε:ℝ) (positive:0<ε):
    ∃ floor:ℕ,∀ᶠ r in trail,let Z:=adjusted F P V A r
    ∀ (k:ℕ),floor≤k → ∀ (upto:k ≤ Z.station.k) (N p:ℕ) (live:Z.station.k<N),
    filed R Z k N p (upto.trans live.le) ε := by
  have homes:=open_late R.family simple 6
  have doors:=WilsonThermometerOffsetLedger.original R simple shop 6
  have steps:∀ᶠ k:ℕ in atTop,∀ e:Fin 7,R.family.ref e≤k:=eventually_all.mpr fun e=>eventually_ge_atTop _
  obtain ⟨floor,ready⟩:=eventually_atTop.mp (homes.and (doors.and steps))
  refine ⟨floor,?_⟩
  filter_upwards [WilsonAddressedCorrectedAlignedFare.original F P V A simple paid lead ε positive] with t cost
  let Z:=adjusted F P V A t
  dsimp only
  intro k lower upto N p live
  have hk:=upto.trans live.le
  obtain ⟨aperture,entry,refs⟩:=ready k lower
  obtain ⟨Q,r,enrolled⟩:=enroll R.makes entry.1 hk (digits R N p 0)
  refine ⟨Q,r,aperture p,enrolled,?_⟩
  intro s
  let x:=Z.station.wheel.atCut (N,p) (index Z (grade 0)) (vector Z s 0)
  have starts(e:ℕ)(leaved:e≤6):R.family.ref e≤N:=(refs ⟨e,by omega⟩).trans hk
  obtain ⟨exactly,spent⟩:=WilsonAddressedAlignedColumn.original R enrolled hk le_rfl starts (aperture p) x
  have price:=cost N p live s 0 k (aperture p).post upto
  exact ⟨exactly,spent.trans (mul_le_mul_of_nonneg_left price (by norm_num))⟩

end YM.Integration.WilsonAddressedCorrectedAlignedSource
end
