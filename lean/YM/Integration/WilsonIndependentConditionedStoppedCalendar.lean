import YM.Integration.WilsonAddressedPublicFirstRoseSchedule
import YM.Integration.WilsonIndependentConditionedStoppedSocket
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedStoppedCalendar
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


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS


open Analysis XSpace Cells Table Spec Extraction
open WilsonOriginalTwoFlatIRCapturedCross (Quote)
open WilsonReceivedChronologicalFixedCellFee (capture factor)
open WilsonAddressedPublicFirstRoseGeometry (Fits)
open WilsonPositionProgramReporterBand (Band)


open Pert.Asymptotics
local notation "β₀" => R.family.path.levels.clock.hatBeta
local notation "mesh" => R.family.S.a
local notation "scale" => R.family.S.scale

open WilsonAddressedPublicFirstRoseSchedule (allowance)

omit [DecidableEq I] [Nonempty I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (world:XSpace.Run){stage u infrared:ℕ}(run:Band R world stage)
    (v:WilsonIndependentCapturedPages.Stop R world run u infrared)(positive:0 < stage)(deep:0 < infrared)
    (cu:R.family.ref 0 ≤ u)(power floor:ℕ){n:ℕ}(φ:Test n){hi:ℝ}(hp:0 < hi)
    (D T h reserve:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    let width:=allowance R simple slow T h reserve infrared
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ}, (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
      (∃i,(ρ i).val=r) →
      let f:=berth R 5 (univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k)
      let K:=berth R reserve f
      let c:=capture R φ r
      ∃w:ℕ,∃_center:c=run.reporter+w,∃uc:u ≤ c,∃vc:v.date w ≤ c,
        let first:=v.date w-1
        first+1=v.date w ∧ u ≤ v.date w ∧ stage ≤ v.date w ∧ floor+1 ≤ c ∧
        c≤f ∧ v.date w < WilsonIndependentConditionedGramSpatialHost.date R simple r ∧
        WilsonAddressedPublicFirstRoseTicket.Receipt R hi (factor R φ) r (wilson z r) first f K c width ∧
        ∀N per:ℕ,c<N → Quote R N per u (v.date w) c power infrared uc vc:=by
  intro width
  obtain ⟨warm,cold⟩:=eventually_atTop.mp (WilsonIndependentConditionedStoppedSocket.cold R simple φ)
  obtain ⟨purchased,heard⟩:=eventually_atTop.mp v.heard
  let reserveFloor:=max floor (max warm (run.reporter+purchased))
  have sale:=WilsonAddressedPublicFirstRoseSchedule.original F simple bliss slow ready world run v positive deep cu power
    reserveFloor φ hp D T h reserve d books
  filter_upwards [sale] with r booked
  intro ρ limits present f K c
  obtain ⟨w,center,uc,vc,number,uv,stageAt,shelf,cf,receipt,quote⟩:=booked ρ limits present
  have large:max floor (max warm (run.reporter+purchased))+1≤c:=shelf
  have raised:purchased≤w:=by omega
  have entry:run.reporter+w≤c:=center.ge
  obtain ⟨hg,hs,paid,_⟩:=(heard w raised).2 c 0 entry
  rw [←center] at hg hs paid
  have temperature:8*WilsonOriginalPublicRelativeGramKineticMesh.thermal R c<factor R φ:=cold c (by omega)
  have opening:factor R φ*r ≤ R.family.S.a 0:=((mul_le_mul_of_nonneg_right (le_max_right hi (factor R φ))
    receipt.positive.le).trans receipt.coarse).trans (R.family.S.strictAnti.antitone (Nat.zero_le _))
  have vm:=WilsonIndependentConditionedStoppedSocket.fits R simple φ receipt.positive opening deep
    (N:=c) (per:=0) le_rfl temperature hg hs paid
  exact ⟨w,center,uc,vc,number,uv,stageAt,by omega,cf,vm,receipt,quote⟩

end YM.Integration.WilsonIndependentConditionedStoppedCalendar
