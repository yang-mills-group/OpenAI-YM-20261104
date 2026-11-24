import YM.Integration.WilsonOriginalTwoFlatPublicMixedMesh
import YM.Integration.WilsonAddressedPublicFirstRoseMovingDate

/-! The actual before-cutoff infrared appointment and its public reporting
grid fit both compact support bounds on the same physical scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFirstRosePublicStops
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

omit [DecidableEq I] [Nonempty I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (world:XSpace.Run){stage u infrared:ℕ}(run:Band R world stage)
    (v:WilsonIndependentCapturedPages.Stop R world run u infrared)(positive:0 < stage)(deep:0 < infrared)
    (cu:R.family.ref 0 ≤ u)(power floor:ℕ){n:ℕ}(φ:Test n){hi lo:ℝ}(hp:0<hi)(lp:0<lo)
    (D T h:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ}, (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
      (∃i,(ρ i).val=r) →
      let f:=berth R 5 (univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k)
      let c:=capture R φ r
      ∃w:ℕ,∃_center:c=run.reporter+w,∃uc:u ≤ c,∃vc:v.date w ≤ c,
        let first:=v.date w-1
        first+1=v.date w ∧ u ≤ v.date w ∧ stage ≤ v.date w ∧ floor+1 ≤ c ∧
        Fits R.family.S hi r first f ∧ Fits R.family.S lo r first f ∧
        ∀N per:ℕ,c<N → Quote R N per u (v.date w) c power infrared uc vc:=by
  obtain ⟨k,earned⟩:=eventually_atTop.mp v.heard
  let floor₁:=max floor (run.reporter+k)
  obtain ⟨rad,rp,booked⟩:=WilsonOriginalTwoFlatIRSocketAppointment.original R simple slow.2 ready world run v cu power φ floor₁
  have fits:=WilsonAddressedPublicFirstRoseMovingDate.original R simple world run v φ deep
    (wilson_link F simple bliss.budgets bliss.keen bliss.lies) hp lp
  filter_upwards [Ioc_mem_nhdsGT rp,fits,WilsonOriginalTwoFlatPublicMixedMesh.original F simple bliss slow D T h d books]
    with r small housed printed
  intro ρ span root f c
  obtain ⟨w,eq,uc,vc,limit,_starting,pass⟩:=booked r small.1 small.2
  have away:run.reporter+k ≤ c:=(le_max_right floor _).trans (Nat.le_of_succ_le limit)
  have kw:k≤w:=by change c=run.reporter+w at eq;omega
  have age:stage ≤ v.date w:=(run.ready w).trans (v.lower w)
  have date:v.date w-1+1=v.date w:=Nat.sub_add_cancel (positive.trans_le age)
  have back:w=c-run.reporter:=by change c=run.reporter+w at eq;omega
  have house:=housed (v.date w-1) f (by rw [←back];exact date) (printed ρ span root).1
  exact ⟨w,eq,uc,vc,date,(earned w kw).1,age,
    (Nat.succ_le_succ (le_max_left floor _)).trans limit,house.1,house.2,pass⟩

end YM.Integration.WilsonAddressedPublicFirstRosePublicStops
end
