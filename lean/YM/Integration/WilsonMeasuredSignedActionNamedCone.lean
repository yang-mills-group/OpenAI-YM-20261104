import YM.Integration.WilsonMeasuredSignedActionEnrolled
import YM.Integration.WilsonMeasuredSignedActionBookedReturn
import YM.Integration.WilsonPositionProgramTrialPublicJointFourBookedReceipt
/-! The named action on the actual previously filed physical mixed
programme, at its ordered regulator limit. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionNamedCone
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
variable {programme:Campaign R}(L:Pillars R programme)

include L in
omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {base:ℕ}(Γ:WilsonViewerReportingGrid.Grid (ℓ:=l) F base (wilson z))
    (D T h τ:ℕ)(deep:2*(2*(2*Γ.stage+2)+3)≤τ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)(fourPaid:4≤D)
    (growing:∀j:ℕ,∀ᶠr in trail,∀p:0<r,∀small:r<δ,
      j≤(books ⟨r,p,small⟩).k ∧ j≤(books ⟨r,p,small⟩).W.k)
    (v₀:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v₀ R.kit)
    {cap k u e:ℕ}(fit:4<cap)(rails:Rails 4 k u e)(enough:4≤k)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>4) (fun _=>cap) (fun _=>fit))≤k)
    {J:ℝ→tower S}{position:ℝ→Spin.change S 4}{bias g:ℝ→ℝ}
    (prepared:∀ᶠr in trail,J r 4=position r)(current:TendC F position bias)(heat:Coupling G g)
    (wide:∀j,1≤((C).path.levels.budget j).supportExponent)
    (X Z:Zoom)(inside:∀m,Z.r m<δ)(ρ:ℕ→I→{s:ℝ // 0<s ∧ s<δ})
    (placed:∀m i,X.r m≤(ρ m i).val ∧ (ρ m i).val≤outer z h (X.r m))(near:∀m,∃i,(ρ m i).val=X.r m)
    (name:I)(location:∀m,ρ m name=⟨Z.r m,Z.positive m,inside m⟩)
    {n:ℕ}{grade:Fin n→ℕ}(E:∀m,Packet R grade (top F books τ (ρ m)))(i:Fin n)(four:grade i=4)
    (home:∀m,(E m).file.station i=(books ⟨Z.r m,Z.positive m,inside m⟩).W.k)
    (q:ℕ)(low:2≤q)(high:q≤e)(unit:Address→ℂ){ω:Filter Address}[NeBot ω](orderly:ω≤atTop.curry order.fuse)
    {v:(F₄).Coeff}{A:Module.End ℂ ((Bel (C).book).Field 4)}(native:Native C A)
    (ident:posted C v=A (stepField C)):
    let B:=fun m=>books ⟨Z.r m,Z.positive m,inside m⟩
    let issued:=fun m=>attach R (E m) i four (weak R F (B m) fourPaid (J (Z.r m)))
    Tendsto (fun p:Address=>(issued p.1).measured fit k ((C).localSection 4) (Γ.date (X.r p.1))
      p.2 i four q (unit p)) ω (𝓝 v) →
    ∃s:ℝ,0 ≤ s ∧ ∃c:ℂ,A (stepField C)=(s:ℂ) • stepField C + c • (Bel (C).book).unit 4:=by
  intro B issued observed
  obtain ⟨roofs,stages⟩:=WilsonMeasuredSignedActionBookLimits.scheduled R F books growing Z inside
  have later(m:ℕ):(B m).W.k<top F books τ (ρ m):=by
    have cost:=WilsonMeasuredSignedActionBookedReturn.after F books τ (ρ m) name
    rw [location m] at cost
    exact cost
  have sign:=WilsonMeasuredSignedActionObserved.original R F L simple bliss prepared current heat Z B
    roofs stages fourPaid wide issued i four home later
    (fun m=>WilsonMeasuredSignedActionEnrolled.plain R (E m) i four _)
    (fun m b=>WilsonMeasuredSignedActionEnrolled.named R (E m) i four _ b)
  exact WilsonMeasuredSignedActionBookedReturn.original F simple bliss slow Γ D T h τ deep d books
    v₀ funded fit rails enough capacity ((C).localSection 4) (R.makes.sections 4) (FVAAlt2.Block.clothes R 4)
    X ρ placed near issued i four q low high unit orderly sign observed native ident

end YM.Integration.WilsonMeasuredSignedActionNamedCone
end
