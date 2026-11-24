import YM.Integration.WilsonAddressedPublicFirstRoseSelected
import YM.Integration.WilsonOriginalOpticalCouplingBand
import YM.Integration.WilsonAddressedPublicFirstRoseSchedule
import YM.Integration.WilsonAddressedPublicFirstRoseWindow
/-! The actual school release is valid at the selected infrared date minus
one, with the true field and the two real flat ears. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseGridStops
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
    (D T h reserve:ℕ)(d:I→Fin (D+1)){δ:ℝ}{School:ℕ→Prop}(academy:∀ᶠm in atTop,School m)
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
        School first ∧ first+1≤K-2 ∧ K-2+1+1=K ∧ v.date w<c ∧ c<f ∧ f<K ∧
        Fits R.family.S hi r first f ∧ Fits R.family.S (factor R φ) r first f ∧ WilsonAddressedPublicFirstRoseTicket.Receipt R hi (factor R φ) r (wilson z r) first f K c width ∧
        ∀N per:ℕ,K≤N → Quote R N per u (v.date w) c power infrared uc vc:=by
  classical
  intro width
  obtain ⟨paid,hits⟩:=eventually_atTop.mp v.heard
  obtain ⟨warm,cold⟩:=eventually_atTop.mp (WilsonOriginalOpticalCouplingBand.cold R simple 2)
  let earlier:=max floor (max (run.reporter+paid) warm)
  have eligible:=WilsonAddressedPublicFirstRoseSelected.original F simple bliss slow ready world run v positive deep cu
    power earlier φ hp D T h reserve d academy books
  filter_upwards [eligible] with r priced
  intro ρ doses attained f K c
  obtain ⟨w,eq,uc,vc,representation,uv,stagePaid,later,taught,tall,atTop,cf,receipt,billed⟩:=priced ρ doses attained
  let first:=v.date w-1
  have lowerReached:run.reporter+paid≤earlier:=(le_max_left ..).trans (le_max_right ..)
  have thermal:warm≤earlier:=(le_max_right ..).trans (le_max_right ..)
  have mature:earlier≤c:=(Nat.le_succ _).trans later
  have paidAt:paid≤w:=by omega
  let γ:=regulatorRun R.family c 0 c
  have pos:0<γ:=ActualRunKernelPackets.regulator_pos R c 0 c le_rfl
  have cheap:(2:ℝ)≤γ⁻¹:=cold c (thermal.trans mature) c 0 le_rfl
  have less:γ<1:=by
    rw [le_inv_comm₀ (by norm_num) pos] at cheap
    linarith
  have actual:=((hits w paidAt).2 c 0 (by omega)).2.2.1
  have before:v.date w<c:=by
    apply lt_of_le_of_ne vc
    intro same
    rw [←eq,same,div_self (R.family.S.a_pos c).ne'] at actual
    exact not_lt_of_ge actual (pow_lt_one₀ (pow_nonneg pos.le _) (pow_lt_one₀ pos.le less deep.ne') (by decide))
  obtain ⟨upperFit,lowerFit⟩:=WilsonAddressedPublicFirstRoseGeometry.original R.family.S hp
    (WilsonReceivedChronologicalFixedCellFee.positive R φ) receipt.positive receipt.coarse receipt.refined
  have margin:8*R.family.S.a f<R.family.S.a c:=lowerFit.margin
  have strictly:c<f:=by
    by_contra! rev
    have reverse:=R.family.S.strictAnti.antitone rev
    linarith only [margin,reverse,R.family.S.a_pos f]
  have top:f<K:=(WilsonInvariantActionPosition.arrival R reserve f).1
  have minAge:floor≤earlier:=le_max_left .. 
  refine ⟨w,eq,uc,vc,representation,uv,stagePaid,(Nat.succ_le_succ minAge).trans later,taught,tall,atTop,
    before,strictly,top,upperFit,lowerFit,receipt,?_⟩
  intro N per live
  exact billed N per (strictly.trans_le (top.le.trans live))

end YM.Integration.WilsonReceivedChronologicalFixedRoseGridStops
end
