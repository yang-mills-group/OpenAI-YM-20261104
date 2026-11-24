import YM.Integration.WilsonPhysicalWeakSundial
import YM.Integration.WilsonPhysicalWeakSameStation

/-! The same original weak turn tends to the elected X-calibrated frame on bounded measured coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalWeakElectedCoordinates
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare

open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {z:Trace.Terrace.Arch R.family}
local notation "C" => R.family
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourSquare

open WilsonAddressedPublicCardBooks (Housed)
open WilsonPhysicalWeakWallStaff (Seats Booked)
open private castArm from YM.Integration.WilsonAddressedPublicCardBooks

open PhysMS PhysMS.Frame
open WilsonPhysicalWeakRisingStaff WilsonPhysicalWeakWallBounded
open WilsonPhysicalWeakWallBooks WilsonPhysicalWeakSameStation WilsonPhysicalWeakSundial

theorem continuousCost (d:ℕ):Continuous fun v:(Bel R.family.book).Field d=>WilsonPhysicalWeakWallBounded.cost R.family v:=by
  unfold WilsonPhysicalWeakWallBounded.cost
  apply continuous_finsetSum _ fun i _=>?_
  change Continuous (fun v=>‖((Module.finBasis ℂ ((Bel R.family.book).Field d)).coord i) v‖)
  exact (LinearMap.continuous_of_finiteDimensional _).norm

variable (simple:G.Simple)(day:ℝ→WilsonPhysicalWeakRisingStaff.Day R.family S)
    (rise:Tendsto (fun r=>(day r).1) trail atTop)
    (sale:∀ᶠr in trail,Served (Y:=l) simple F H (day r) r)
    {D T:ℕ}{δ:ℝ}
    (books:(r:{r:ℝ//0<r ∧ r<δ})→Book F (l:=l) H z D T r.val)
    (shared:∀r,∃cap:D≤(day r.val).1,Shared F (books r) (trim cap (day r.val).2))
    {ι:Type*}(u:Filter ι)(age:ι→{r:ℝ//0<r ∧ r<δ})(near:Tendsto (fun i=>(age i).val) u trail)

include sale rise shared near in
theorem provision (m:ℕ):
    ∀ᶠi in u,∀j:Fin (D+1),∀v:(Bel R.family.book).Field j,
    ‖((books (age i)).V j).symm (provisional day (age i).val j v)-v‖≤WilsonPhysicalWeakWallBounded.cost R.family v*costHint m:=by
  filter_upwards [near.eventually sale,near.eventually (rise.eventually_ge_atTop m)] with i sold live j v
  obtain ⟨cap,bought⟩:=shared (age i)
  have issued:=WilsonPhysicalWeakSameStation.admitted F cap live simple (day (age i).val).2 sold
  have basis(k:Fin (Module.finrank ℂ ((Bel R.family.book).Field j))):
      ‖(trim cap (day (age i).val).2).room.change j (Module.finBasis ℂ _ k)-Module.finBasis ℂ _ k‖≤costHint m:=
    ((issued.2.2 m le_rfl).2).2.2.2.2.2 ⟨j,k⟩
  have rooted:=atBasis (Module.finBasis ℂ _) ((trim cap (day (age i).val).2).room.change j) (costHint m) basis v
  rw [issued.2.1 j] at rooted
  rw [bought.2.2.2]
  exact rooted

variable (J:ℝ→tower S)(link:localCost trail (provisional day) J)
include sale rise shared near link in
theorem oriented (j:Fin (D+1))(v:(Bel R.family.book).Field j):
    Tendsto (fun i=>((books (age i)).V j).symm (J (age i).val j v)) u (𝓝 v):=by
  let y (i:ι):=(provisional day (age i).val j).symm (J (age i).val j v)
  have tends:Tendsto y u (𝓝 v):=(link j v).comp near
  have purse:Tendsto (fun i=>WilsonPhysicalWeakWallBounded.cost R.family (y i)) u (𝓝 (WilsonPhysicalWeakWallBounded.cost R.family v)):=(continuousCost (R:=R) j).continuousAt.tendsto.comp tends
  have cap:=purse.eventually_lt_const (lt_add_one (WilsonPhysicalWeakWallBounded.cost R.family v))
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  have prices:=cost_clears.const_mul (WilsonPhysicalWeakWallBounded.cost R.family v+1)
  rw [mul_zero] at prices
  obtain ⟨m,small⟩:=(prices.eventually_lt_const (half_pos ep)).exists
  have known:=provision F simple day rise sale books shared u age near m
  filter_upwards [cap,known,Metric.tendsto_nhds.mp tends (ε/2) (half_pos ep)] with i income ok direct
  have tagged:provisional day (age i).val j (y i)=J (age i).val j v:=LinearEquiv.apply_symm_apply _ _
  have first:=ok j (y i)
  rw [tagged] at first
  have below:dist (((books (age i)).V j).symm (J (age i).val j v)) (y i)<ε/2:=by
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (first.trans (mul_le_mul_of_nonneg_right income.le (cost_pos m).le)) small
  calc
    _≤dist (((books (age i)).V j).symm (J (age i).val j v)) (y i)+dist (y i) v:=dist_triangle _ _ _
    _<ε/2+ε/2:=add_lt_add below direct
    _=ε:=add_halves ε

end YM.Integration.WilsonPhysicalWeakElectedCoordinates
