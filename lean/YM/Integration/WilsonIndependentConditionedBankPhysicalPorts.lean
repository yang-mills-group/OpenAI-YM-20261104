import YM.Integration.WilsonIndependentConditionedBankObservedPorts
import YM.Integration.WilsonIndependentConditionedGramSplitPooled

/-! Select both actual physical preparations at their own stations, preserving each measured return on its original arm. -/
set_option warningAsError true
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankPhysicalPorts
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
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS


open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open WilsonThermometerMarchSource WilsonThermometerReflectedTrajectory WilsonMeasuredPublicEntranceHeadBoard
open WilsonAddressedAlignedColumn WilsonReflectedPublicStationFare
open WilsonThermometerOffsetCylinder WilsonThermometerOffsetTrajectory


open WilsonReflectedMixedMasterAxes (Fixed)
open WilsonReflectedMixedThermalArms (rent)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)

open WilsonReflectedMixedMasterRegistry (Gallery Delivery)
open WilsonOriginalMicroscopicGuardedReporters (Arrived)
open WilsonIndependentConditionedBankSeats (Resident)
open WilsonReflectedMixedObservedArms (Printed)
open WilsonReflectedFundedHearing (Arm)

open WilsonReflectedMixedLocatedSchool (Paid)
open WilsonMovingForkOpticalBook (reporter)
open WilsonIndependentConditionedGramSplitPooled (marked)
open WilsonIndependentConditionedBankSeats (restored submitted)
open WilsonIndependentNotebookConstantSeat (seat)
open WilsonIndependentMatchedFiledIncome (charge plate)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Fountain WilsonCoeffUV.Soil

omit [Fintype I] [DecidableEq I] [Nonempty I] in
theorem issued (D T h t:ℕ)(d:I→Fin (D+1))(e:I→ℕ){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (probe:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    (M:I→ℝ)(ceiling η:ℝ)(power target:ℕ)(ρ:I→{s:ℝ // 0<s ∧ s<δ})(f K:ℕ)
    (bought:WilsonReflectedMixedObservedPanel.Received F D T h t d e books probe M ceiling η power target ρ f K):
    ∃up:f<K,∀N per(live:K ≤ N),
      let L:=fun i=>(books (ρ i)).rows (d i)
      let j:=fun i b=>WilsonReflectedPublicStationFare.station F (L i) b
      ∃axes:(i:I)→Bool→(C).label (d i).val≃ₗ[ℂ](C).label (d i).val,
      ∀(fields:(i:I)→Bool→S.Field (d i).val)(turn:I→Bool→Signed)(hand:I→Bool→Bool)
        (loc:I→Bool→Site ((C).side f per))(phase:I→Bool→ℂ),
      ∃r:(i:I)→Bool→Resident R (d i).val f K N per target up.le live η,∀i b,
        (r i b).station=j i b ∧ (r i b).axis=axes i b ∧ (r i b).source=((L i).arm b (fields i b)).source (N,per) ∧
        (r i b).salary=WilsonReflectedPublicStationFare.fee F (L i) b (fields i b) ∧
        (r i b).phase=phase i b ∧ Printed R (j i b) (axes i b) (((L i).arm b (fields i b)).source (N,per))
          (turn i b) (hand i b) (loc i b) (r i b).arm:=by
  classical
  obtain ⟨up,receipts⟩:=WilsonIndependentConditionedBankObservedPorts.original F D T h t d e books probe M
    ceiling η power target ρ f K bought
  refine ⟨up,?_⟩
  intro N per live L j
  obtain ⟨first,axes,individual,_⟩:=receipts N per live
  refine ⟨axes,?_⟩
  intro fields turn hand loc phase
  choose r hr using fun i b=>WilsonIndependentConditionedBankObservedPorts.placed (individual i b (fields i b))
    (turn i b) (hand i b) (loc i b) (phase i b)
  exact ⟨r,hr⟩

omit [DecidableEq I] [Nonempty I] in
theorem received {D T:ℕ}(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)(ρ:I→{s:ℝ // 0<s ∧ s<δ})
    (phys:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→S.Field (d i).val)
    (i:I)(b im:Bool)(η:ℝ)(α:ℂ){K N per target q:ℕ}
    {up:reporter F books ρ ≤ K}{live:K ≤ N}
    (r:Resident R (d i).val (reporter F books ρ) K N per target up live η)
    (station:r.station=WilsonReflectedPublicStationFare.station F ((books (ρ i)).rows (d i)) b)
    (salary:r.salary=WilsonReflectedPublicStationFare.fee F ((books (ρ i)).rows (d i)) b (phys i (ρ i) b))
    (phase:r.phase=α)(I₀:XSpace.Initialize G)(survey:Bool)(top:ℕ)(fit:(d i).val<top)
    (A:Alma (R.family.labels.level (d i).val)→ℝ)(nn:∀j,0 ≤ A j):
    let F₀:=R.family.labels.level (d i).val
    let c:=((q+1:ℕ):ℝ)*∑j:F₀.Index,A (seat F₀ j)
    let γ:=R.family.S.a K/R.family.S.a (reporter F books ρ)
    charge q (submitted r im) A ≤ (marked F books ρ phys b η α i*c)*γ^(-η):=by
  intro F₀ c γ
  have bill:=(WilsonIndependentConditionedBankSeats.paid (e:=q) r I₀ survey fit A nn im).2.2
  apply bill.trans_eq
  unfold restored WilsonIndependentConditionedGramSplitPooled.marked
  rw [station,salary,phase]
  dsimp only [c,F₀,γ]
  ring

end YM.Integration.WilsonIndependentConditionedBankPhysicalPorts
