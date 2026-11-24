import YM.Integration.WilsonAddressedMixedStationRange
import YM.Integration.WilsonMeasuredPublicEntranceFittedSlots
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonAddressedMixedStationPages
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


open Function Filter Lattice Wilson RG Source Labels
open Extraction Table Spec Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Work.G08
open Next.Foundations OPE.Therm Push.AbsoluteSums.Animals
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonAddressedRestartedColumn WilsonOriginalNullCorridor WilsonPositionProgramOriginalBlockedTrial
open WilsonMeasuredPublicEntranceGridDebit WilsonOriginalMicroscopicGuardedReporters
open WilsonPositionHomogeneousFrame WilsonThermometerUnitFilingFourSquare
open WilsonPositionProgramBlockedPublicExperiment WilsonAddressedPublicPool
open scoped Classical BigOperators

omit [Fintype I] [DecidableEq I] [Nonempty I] in
theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1 ≤ ((C).path.levels.budget j).supportExponent)(quote:Poetry (C).path.levels)
    (D target:ℕ){η:ℝ}(pos:0<η):
    ∃gate:ℕ,∀(T:ℕ)(d:I→Fin (D+1)){δ:ℝ}
      (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
      (ρ:I→{s:ℝ // 0<s ∧ s<δ})(branch:I→Bool)(v:(i:I)→S.Field (d i).val)
      (f n N p:ℕ)(live:f+n ≤ N),
      let L:=fun i=>(books (ρ i)).rows (d i)
      let j:=fun i=>WilsonReflectedPublicStationFare.station F (L i) (branch i)
      let Y:=fun i=>((L i).arm (branch i) (v i)).source (N,p)
      let J:=fun i=>WilsonReflectedPublicStationFare.fee F (L i) (branch i) (v i)
      (∀i,gate ≤ j i)→∀(before:∀i,j i ≤ f), (∀i,j i<N) →
      ∃A:(i:I)→(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val,
      (∀i x,Arrived R (d i).val (j i) (f+n) N p target (by grind) live η (A i) x) ∧
      ∀i,let w:=(A i).symm (fitted R (d i).val (j i) N p (Y i))
        ((C).labels.level (d i).val).coeffSize w  ≤  stretch R η (j i) (f+n)*(2*(a (j i)^(d i).val*J i)) ∧
          ∀o,settled R (d i).val (j i) f n N p live (A i) (Y i) o:=by
  classical
  obtain ⟨g,sale⟩:=WilsonMeasuredPublicEntranceGridDebit.original R simple shop wide quote D target pos
  have opened:∀k:Fin (D+1),∀ᶠ j:ℕ in atTop,∀p,Opened C k.val j p:=fun k=>open_late C simple k.val
  obtain ⟨b,ready⟩:=eventually_atTop.mp (Filter.eventually_all.mpr opened)
  refine ⟨max g b,?_⟩
  intro T d δ books ρ branch v f n N p live L j Y J late before deep
  obtain ⟨A,rows,got⟩:=sale I d j f n N p (fun i=>(le_max_left ..).trans (late i)) before live deep
  refine ⟨A,rows,?_⟩
  intro i
  obtain ⟨ref,rate⟩:=WilsonReflectedPublicStationFare.original F (L i) (books (ρ i)).checked (branch i) (v i)
  let x:=((C).factory (d i).val N p).terminal.symm (Y i)
  let q:=((C).factory (d i).val N p).entries (j i) x
  have priced:((C).labels.level (d i).val).coeffSize q.x  ≤  a (j i)^(d i).val*J i:=by
    simpa only [Next.UVStress.quota,Y,x,q,J,j] using rate N p (deep i)
  have pagePrice:=(size_gap (d i).val N p (j i) R.makes
    (ready (j i) ((le_max_right ..).trans (late i)) (d i) p) (deep i).le x).1
  refine ⟨((rows i (fitted R (d i).val (j i) N p (Y i))).1).trans ?_,?_⟩
  · exact mul_le_mul_of_nonneg_left (pagePrice.trans (mul_le_mul_of_nonneg_left priced zero_le_two))
      (by unfold WilsonOriginalMicroscopicGuardedReporters.stretch;positivity)
  · exact got i (ref.trans (before i)) (Y i)

end YM.Integration.WilsonAddressedMixedStationPages
end
