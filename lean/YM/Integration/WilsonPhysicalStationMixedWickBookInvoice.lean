import YM.Integration.WilsonPhysicalStationMixedWickBookIncome
import YM.Integration.WilsonMeasuredSignedActionPosedSchool

/-! Price the already submitted book at all finite grades on an interval of original physical homes. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickBookInvoice
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


open WilsonMeasuredSignedActionOwnedIncome (Issued)
open WilsonMeasuredSignedActionOwnedBook (sub)
open WilsonMeasuredPublicEntranceNativeFrame (atRadius)

open WilsonMeasuredSignedActionReleased (Licensed)

def restrict {δ ε:ℝ}(incl:δ≤ε)(s:{r:ℝ // 0<r ∧ r<δ}):{r:ℝ // 0<r ∧ r<ε}:=
  ⟨s.val,s.property.1,s.property.2.trans_le incl⟩

theorem booked {δ ε:ℝ}(dp:0<ε)(incl:ε≤δ)(cap:Set.Ioc (0:ℝ) δ→ℕ)(V:∀s,Vane C (cap s))(prior:ℝ→tower S)
    (D T:ℕ)(books:(s:{r:ℝ // 0<r ∧ r<ε})→Book F (l:=l) H z D T s.val)
    (owns:∀s,∀d:Fin (D+1),(books s).V d=atRadius l cap V prior s.val d)
    (income:∀ᶠr in trail,∀s:Set.Ioc (0:ℝ) δ,s.val=r→WilsonPhysicalStationMixedWickBookIncome.Inverse F (l:=l) (V s) r D):
    ∃η:ℝ,0<η ∧ ∃small:η≤ε,∀s:{r:ℝ // 0<r ∧ r<η},
      WilsonMovingForkWindowBooks.Priced F (books (restrict small s)):=by
  have rates:=WilsonPhysicalStationMixedWickBookIncome.appointed F cap V prior D income
  obtain ⟨η,pos,range⟩:=Metric.mem_nhdsWithin_iff.mp rates
  refine ⟨min η ε,lt_min pos dp,min_le_right _ _,fun s d v=>?_⟩
  let u:=restrict (min_le_right η ε) s
  change ‖((books u).V d).symm v‖≤dock s.val*cost F d s.val v
  rw [owns u d]
  apply range (a:=s.val) _ (WilsonMeasuredSignedActionOwnedBook.sub incl u) rfl d v
  exact ⟨by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos s.property.1] using
    s.property.2.trans_le (min_le_left η ε),s.property.1⟩

omit [DecidableEq I] [Nonempty I] in
theorem licensed {base D T:ℕ}{δ ε:ℝ}(small:δ≤ε)
    (Γ:WilsonViewerReportingGrid.Grid (ℓ:=l) F base (wilson z))
    (books:(s:{r:ℝ // 0<r ∧ r<ε})→Book F (l:=l) H z D T s.val)(J:ℝ→tower S)
    (paid:Licensed F (I:=I) Γ D T books J):Licensed F (I:=I) Γ D T (fun s=>books (restrict small s)) J:=by
  intro h τ deep ds fourPaid v₀ funded cap k u fuel fit rails enough capacity X Z inside ρ placed near name location
    n grade E i four home q low high unit ω clean orderly v A native ident
  let ρ' (m:ℕ)(i:I):{s:ℝ // 0<s ∧ s<ε}:=restrict small (ρ m i)
  have hits(m:ℕ):Z.r m<ε:=(inside m).trans_le small
  have site(m:ℕ):ρ' m name=⟨Z.r m,Z.positive m,hits m⟩:=Subtype.ext (congrArg (fun s:{r:ℝ // 0<r ∧ r<δ}=>s.val) (location m))
  exact paid h τ deep ds fourPaid v₀ funded fit rails enough capacity X Z hits ρ' placed near name site
    E i four home q low high unit orderly native ident

end YM.Integration.WilsonPhysicalStationMixedWickBookInvoice
end
