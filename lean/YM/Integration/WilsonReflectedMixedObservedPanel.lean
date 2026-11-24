import YM.Integration.WilsonReflectedMixedObservedArms
import YM.Integration.WilsonReflectedMixedPortfolioPanel
import YM.Integration.WilsonReflectedMixedTrialDates
set_option warningAsError true
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReflectedMixedObservedPanel
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
def Received (D T h t:ℕ)(d:I→Fin (D+1))(e:I→ℕ){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    (M:I→ℝ)(ceiling η:ℝ)(power target:ℕ)(ρ:I→{s:ℝ // 0<s ∧ s<δ})(f K:ℕ):Prop:=
    ∃up:f<K,∀N p(live:K≤N),
    let L:=fun i=>(books (ρ i)).rows (d i)
    let j:=fun i b=>WilsonReflectedPublicStationFare.station F (L i) b
    ∃(first:∀i b,j i b≤f)(axes:(i:I)→Bool→(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val),
      (∀i (mode b:Bool),Fixed R (d i).val (j i b) target N p f K (e i) (first i b) up.le live
        (((L i).arm b (field i (ρ i) mode b)).source (N,p)) (M i) (ceiling*(β K)^power) (axes i b)) ∧
      (∀i b (v:S.Field (d i).val),WilsonReflectedMixedSharpAxis.Cash (R:=R) (d i).val (j i b) f K N p target (first i b) up.le live η (axes i b)
        (((L i).arm b v).source (N,p)) (WilsonReflectedPublicStationFare.fee F (L i) b v)) ∧
      (∀i b (Λ:Type)[Fintype Λ] (c:Λ→ℂ)(v:Λ→S.Field (d i).val),
        WilsonReflectedMixedSharpAxis.Cash (R:=R) (d i).val (j i b) f K N p target (first i b) up.le live η (axes i b)
          (∑a,c a•((L i).arm b (v a)).source (N,p)) (∑a,‖c a‖*WilsonReflectedPublicStationFare.fee F (L i) b (v a))) ∧
      (∀i b old (η:ℝ) (A:(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val) x,
        Arrived R (d i).val (j i b) K N p old ((first i b).trans up.le) live η A x →
        A.symm x=(axes i b).symm x) ∧
      (∀(parts:I→ℕ)(kind:I→Bool)(v:(i:I)→Fin (parts i)→S.Field (d i).val)
        (c:(i:I)→Fin (parts i)→ℂ)(turn:I→Signed)(hand:I→Bool)(o:I→Site ((C).side f p)),
        Nonempty (WilsonReflectedMixedObservedArms.Filed R (N:=N) (K:=K) (fun i=>j i (kind i)) (fun i=>(d i).val) parts
          (fun i=>axes i (kind i)) (fun i a=>((L i).arm (kind i) (v i a)).source (N,p)) c turn hand o)) ∧
      Gallery F D T h t d books ρ f N p (up.trans_le live)



omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h target:ℕ)(η:ℝ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) →
      (∃i,(ρ i).val=r) →∀(t f K:ℕ)(e:I→ℕ)(field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
      (M:I→ℝ)(cap:ℝ)(power:ℕ),
      WilsonReflectedMixedPortfolioPanel.Received F D T h t d e books field M cap η power target ρ f K →
      Received F D T h t d e books field M cap η power target ρ f K:=by
  filter_upwards [WilsonReflectedMixedTrialDates.original F simple bliss slow D T h d books] with r opens
  intro ρ span near t f K e field M cap power source
  obtain ⟨up,offered⟩:=source
  refine ⟨up,?_⟩
  intro N p live L j
  obtain ⟨first,axes,fixed,individual,portfolio,presold,gallery⟩:=offered N p live
  refine ⟨first,axes,fixed,individual,portfolio,presold,?_,gallery⟩
  intro parts kind v c turn hand o
  exact WilsonReflectedMixedObservedArms.original R up.le live (fun i=>j i (kind i)) (fun i=>(d i).val)
    parts (fun i=>first i (kind i)) (fun i=>opens ρ span near i (kind i) p) (fun i=>axes i (kind i))
    (fun i a=>((L i).arm (kind i) (v i a)).source (N,p)) c turn hand o (fun i a=>individual i (kind i) (v i a))
    (fun i=>portfolio i (kind i) (Fin (parts i)) (c i) (v i))

end YM.Integration.WilsonReflectedMixedObservedPanel
end
