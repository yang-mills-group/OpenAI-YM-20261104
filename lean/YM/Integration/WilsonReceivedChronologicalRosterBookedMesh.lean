import YM.Integration.WilsonReceivedChronologicalRosterReporterGap
import YM.Integration.WilsonOriginalTwoFlatPublicMixedMesh
import YM.Integration.WilsonMovingForkOpticalBook
import YM.Integration.WilsonAddressedPublicFirstRoseMovingDate

/-! The physical reporter and capture radius fitted to the original public names. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterBookedMesh
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
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS

open WilsonMovingForkOpticalBook (reporter)
open WilsonReceivedChronologicalFixedCellFee (factor capture)
open Next.Rank.Station

omit [DecidableEq I] [Nonempty I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h:ℕ)(d:I → Fin (D+1)){δ:ℝ}(books:(s:{s:ℝ // 0 < s ∧ s < δ}) → Book F (l:=l) H z D T s.val)
    {arity:ℕ}(φ:Test arity):
    ∀ᶠr in trail,∀ρ:I → {s:ℝ // 0 < s ∧ s < δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) → 
      let f:=reporter F books ρ
      let c:=capture R φ r
      c+2 ≤ f ∧ a c/a f ≤ (β f)^(2*T+13+2*h):=by
  classical
  let M:=factor R φ
  have mp:0 < M:=WilsonReceivedChronologicalFixedCellFee.positive R φ
  obtain ⟨floor,reserved⟩:=eventually_atTop.mp (WilsonReceivedChronologicalRosterReporterGap.original R simple slow mp)
  obtain ⟨hot,heat⟩:=eventually_atTop.mp ((hat_rate (P) simple).eventually_ge_atTop (3*M))
  let onset:=max floor hot
  filter_upwards [WilsonOriginalTwoFlatPublicMixedMesh.original F simple bliss slow D T h d books,
    Ioc_mem_nhdsGT (div_pos (R.family.S.a_pos 0) mp),
    Ioc_mem_nhdsGT (R.family.S.a_pos (onset+1))] with r quoted room small
  intro ρ span anchor f c
  let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
  obtain ⟨i,near⟩:=anchor
  have im:(books (ρ i)).W.k ≤ m:=(le_max_right ..).trans
    (Finset.le_sup (f:=fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k) (mem_univ i))
  have am:a m ≤ r:=((C).S.strictAnti.antitone im).trans
    (((WilsonReflectedPublicBulbBerth.mesh R _ (books (ρ i)).checked).trans (books (ρ i)).active.le).trans near.le)
  have late:onset ≤ m:=by
    by_contra! early
    exact (not_lt_of_ge (am.trans small.2)) ((C).S.strictAnti (by omega:m < onset+1))
  have live:M*r ≤ a 0:=by simpa only [mul_comm] using (le_div_iff₀ mp).mp room.2
  have proper:=WilsonCloseCaptureDate.bracket R.family.S (mul_pos mp room.1) live
  have advanced:c+2 ≤ f:=reserved m ((le_max_left ..).trans late) am proper.2
  have mf:m ≤ f:=(WilsonInvariantActionPosition.arrival R 5 m).1.le
  have mk:3*M ≤ β f:=heat f (((le_max_right ..).trans late).trans mf)
  have entry:r ≤ (β f)^(2*T+11+2*h)*a f:=near ▸ (quoted ρ span ⟨i,near⟩).2 i
  have cost:=WilsonAddressedPublicFirstRoseCaptureWidth.original R simple slow room.1 mp
    (by omega:c ≤ f) proper.1 mk entry
  exact ⟨advanced,by simpa only [show 2*T+11+2*h+2=2*T+13+2*h by omega] using cost⟩

end YM.Integration.WilsonReceivedChronologicalRosterBookedMesh
