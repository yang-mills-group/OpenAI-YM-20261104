import YM.Integration.WilsonIndependentConditionedBankSeats
import YM.Integration.WilsonReflectedMixedObservedPanel

/-! The received four-corner measurements use the same original axes and fields at every real or imaginary component. -/
set_option warningAsError true
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankObservedPorts
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

variable {d₀ j₀ f K N per target:ℕ}{up:f ≤ K}{live:K ≤ N}{η:ℝ}

def recorded {A:(C).label d₀≃ₗ[ℂ](C).label d₀}{Y:(C).label d₀}{salary:ℝ}{start:j₀ ≤ f}
    {turn:Signed}{hand:Bool}{loc:Site ((C).side f per)}(arm:Arm R d₀ N per f K)
    (cash:WilsonReflectedMixedSharpAxis.Cash (R:=R) d₀ j₀ f K N per target start up live η A Y salary)
    (held:Printed R j₀ A Y turn hand loc arm)(phase:ℂ):Resident R d₀ f K N per target up live η:=
  ⟨j₀,start,A,Y,salary,cash,arm,held.inverse,phase⟩

theorem placed {A:(C).label d₀≃ₗ[ℂ](C).label d₀}{Y:(C).label d₀}{salary:ℝ}{start:j₀ ≤ f}
    (cash:WilsonReflectedMixedSharpAxis.Cash (R:=R) d₀ j₀ f K N per target start up live η A Y salary)
    (turn:Signed)(hand:Bool)(loc:Site ((C).side f per))(phase:ℂ):
    ∃r:Resident R d₀ f K N per target up live η,
      r.station=j₀ ∧ r.axis=A ∧ r.source=Y ∧ r.salary=salary ∧ r.phase=phase ∧
      Printed R j₀ A Y turn hand loc r.arm:=by
  obtain ⟨arm,inlet,inv,sign,sym,site,wage⟩:=WilsonReflectedMixedFundedPortfolio.mounted R cash hand turn loc
  have full:Printed R j₀ A Y turn hand loc arm:=⟨inlet,inv,sign,sym,site,wage⟩
  exact ⟨recorded arm cash full phase,rfl,rfl,rfl,rfl,rfl,full⟩

omit [Fintype I] [DecidableEq I] [Nonempty I] in
theorem original (D T h t:ℕ)(d:I→Fin (D+1))(e:I→ℕ){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    (M:I→ℝ)(ceiling η:ℝ)(power target:ℕ)(ρ:I→{s:ℝ // 0<s ∧ s<δ})(f K:ℕ)
    (bought:WilsonReflectedMixedObservedPanel.Received F D T h t d e books field M ceiling η power target ρ f K):
    ∃up:f<K,∀N per(live:K ≤ N),
      let L:=fun i=>(books (ρ i)).rows (d i)
      let j:=fun i b=>WilsonReflectedPublicStationFare.station F (L i) b
      ∃(first:∀i b,j i b ≤ f)(axes:(i:I)→Bool→(C).label (d i).val≃ₗ[ℂ](C).label (d i).val),
        (∀i b (w:S.Field (d i).val),
          WilsonReflectedMixedSharpAxis.Cash (R:=R) (d i).val (j i b) f K N per target (first i b)
            up.le live η (axes i b) (((L i).arm b w).source (N,per)) (WilsonReflectedPublicStationFare.fee F (L i) b w)) ∧
        ∀i b (Λ:Type)[Fintype Λ](c:Λ→ℂ)(w:Λ→S.Field (d i).val)
        (turn:Signed)(hand:Bool)(loc:Site ((C).side f per))(phase:ℂ),
          let Y:=∑a,c a • (((L i).arm b (w a)).source (N,per))
          let wages:=∑a,‖c a‖*WilsonReflectedPublicStationFare.fee F (L i) b (w a)
          ∃r:Resident R (d i).val f K N per target up.le live η,
            r.station=j i b ∧ r.axis=axes i b ∧ r.source=Y ∧ r.salary=wages ∧ r.phase=phase ∧
            Printed R (j i b) (axes i b) Y turn hand loc r.arm:=by
  obtain ⟨up,issue⟩:=bought
  refine ⟨up,?_⟩
  intro N per live L j
  obtain ⟨first,axes,_,single,whole,_⟩:=issue N per live
  refine ⟨first,axes,single,?_⟩
  intro i b Λ _ c w turn hand loc phase Y wages
  exact placed (whole i b Λ c w) turn hand loc phase

end YM.Integration.WilsonIndependentConditionedBankObservedPorts
