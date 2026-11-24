import YM.Integration.WilsonMeasuredSignedActionReleased
import YM.Integration.WilsonMeasuredSignedActionSmoothLaw
/-! One actual regulated action column and its two normalizing rows. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionOneReturn
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


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS


open WilsonOriginalPublicRelativeGramKineticMesh (thermal)

open RG.Supply Precision Next.Foundations WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels XSpace Extra.Histories Pert.Asymptotics
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonPositionProgramTrialPublicJointFourMixedFitted (field)
open WilsonPositionProgramTrialPublicJointFourMixedIncome (turned)
open WilsonPositionProgramTrialPublicJointFourSignedFitted (coefficient)
local notation "F₄" => R.family.labels.level 4



open WilsonMeasuredSignedActionPacket (Packet top)
open WilsonMeasuredSignedActionAverage (pool)
open WilsonMeasuredSignedActionCourse (axis)
open WilsonMeasuredSignedActionProjected (posted)
open WilsonPhysicalPositionAdmissible (Native)
open TraceExtension Next.UVStress

open Trace.Over Trace.Terrace Trace.Pilot TraceExtension
open WilsonOriginalMicroscopicGuardedReporters MergeProof Campaign
open WilsonMeasuredSignedActionBookedReturn (Address)
open WilsonMeasuredSignedActionRegistry (weak)
open WilsonMeasuredSignedActionEnrolled (attach heardAll)
open WilsonMeasuredPublicEntranceCommonColor (carried)
open WilsonMeasuredPublicEntranceMarkedQuadratics (marked)

open WilsonMeasuredSignedActionReleased (Licensed)
open WilsonPhysicalPositionReflectedReturn (sites)

def light {g:Gauge}(D:Family g)(hs:g.Simple)(H₀:(Bel D.book).Hierarchy):ContDiffBump sites:=
  Classical.choose (WilsonMeasuredSignedActionSmoothPacket.original D hs H₀)

omit [DecidableEq I] [Nonempty I] in
theorem original (simple:G.Simple){base:ℕ}(Γ:WilsonViewerReportingGrid.Grid (ℓ:=l) F base (wilson z))
    (D T h τ:ℕ)(deep:2*(2*(2*Γ.stage+2)+3)≤τ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)(fourPaid:4≤D)
    (v₀:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v₀ R.kit)
    {cap k u e:ℕ}(fit:4<cap)(rails:Rails 4 k u e)(enough:4≤k)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>4) (fun _=>cap) (fun _=>fit))≤k)
    {J:ℝ→tower S}(ticket:Licensed F (I:=I) Γ D T books J)(lead:Leading F J)
    (X Z:Zoom)(inside:∀m,Z.r m<δ)(ρ:ℕ→I→{s:ℝ // 0<s ∧ s<δ})
    (placed:∀m i,X.r m≤(ρ m i).val ∧ (ρ m i).val≤outer z h (X.r m))(near:∀m,∃i,(ρ m i).val=X.r m)
    (name:I)(location:∀m,ρ m name=⟨Z.r m,Z.positive m,inside m⟩)
    {n:ℕ}{grade:Fin n→ℕ}(E:∀m,Packet R grade (top F books τ (ρ m)))(i:Fin n)(four:grade i=4)
    (home:∀m,(E m).file.station i=(books ⟨Z.r m,Z.positive m,inside m⟩).W.k)
    (q:ℕ)(low:2≤q)(high:q≤e)(unit:Address→ℂ){ω:Filter Address}[NeBot ω](orderly:ω≤atTop.curry order.fuse)
    {v:(F₄).Coeff}{A:Module.End ℂ ((Bel (C).book).Field 4)}(native:Native C A)
    (ident:posted C v=A (stepField C))
    (hearing:WilsonMeasuredSignedActionSmoothLaw.Returns F J (light C simple H) (fun p:Address=>Z.r p.1) ω A):
    let B:=fun m=>books ⟨Z.r m,Z.positive m,inside m⟩
    let issued:=fun m=>attach R (E m) i four (weak R F (B m) fourPaid (J (Z.r m)))
    Tendsto (fun p:Address=>(issued p.1).measured fit k ((C).localSection 4) (Γ.date (X.r p.1))
      p.2 i four q (unit p)) ω (𝓝 v) →
    A (stepField C)=stepField C ∧ carried C A (marked G (le_refl 4) 1)=marked G (le_refl 4) 1:=by
  intro B issued reading
  have panel:=Classical.choose_spec (WilsonMeasuredSignedActionSmoothPacket.original C simple H)
  have small:Tendsto Z.r atTop trail:=tendsto_nhdsWithin_iff.mpr ⟨Z.limits,Eventually.of_forall Z.positive⟩
  have bought:=WilsonMeasuredSignedActionSmoothLaw.heard F J lead (light C simple H) panel.1
    (small.comp ((WilsonMeasuredSignedActionBookedReturn.first order.fuse).mono_left orderly)) hearing
  apply WilsonMeasuredSignedActionSmoothTest.fixed C H _ panel.2 A bought
  exact ticket h τ deep d fourPaid v₀ funded fit rails enough capacity X Z inside ρ placed near name location
    E i four home q low high unit orderly native ident reading

end YM.Integration.WilsonMeasuredSignedActionOneReturn
end
