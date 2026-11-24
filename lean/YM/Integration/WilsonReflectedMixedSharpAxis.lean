import YM.Integration.WilsonReflectedMixedPrescribedSchool
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonReflectedMixedSharpAxis
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


/-- Physical and numerical fares of the same original inverse at the sharper
reserve. Its denominator is the once-normalized true occupied source. -/
def Cash (d j f K N p target:ℕ)(before:j≤f)(up:f≤K)(live:K≤N)(η:ℝ)
    (A:(C).label d≃ₗ[ℂ](C).label d)(Y:(C).label d)(W:ℝ):Prop:=
  (∀x,Arrived R d j K N p target (before.trans up) live η A x) ∧
  let w:=A.symm (fitted R d j N p Y)
  ((C).labels.level d).coeffSize w ≤ stretch R η j K*(2*(a j^d*W)) ∧
  (∀o,settled R d j f (K-f) N p (by rw [Nat.add_sub_of_le up];exact live) A Y o) ∧
  ∀χ:ℝ,0<χ→((C).labels.level d).coeffSize (WilsonAddressedPublicGuardFare.word R d K χ w) ≤
    4*(W/χ)*(a j/a K)^((d:ℝ)+η)

/-- Choose the sharp date threshold before any books, fields or regulators.
The returned income is on the previously funded finite Wilson inverse. -/
theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1≤((C).path.levels.budget j).supportExponent)(quote:Poetry (C).path.levels)
    (D target:ℕ){η:ℝ}(pos:0<η):
    ∃gate:ℕ,∀T{δ:ℝ}(books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
      (ρ:{s:ℝ // 0<s ∧ s<δ})(d:Fin (D+1))(b:Bool)(v:S.Field d.val)(f K N p:ℕ)
      (up:f<K)(live:K≤N),
      let L:=(books ρ).rows d
      let j:=WilsonReflectedPublicStationFare.station F L b
      ∀(_late:gate≤j)(before:j≤f){old:ℕ}{oldReserve:ℝ}(A:(C).label d.val≃ₗ[ℂ](C).label d.val),
      (∀x,Arrived R d.val j K N p old (before.trans up.le) live oldReserve A x) →
      Cash (R:=R) d.val j f K N p target before up.le live η A ((L.arm b v).source (N,p))
        (WilsonReflectedPublicStationFare.fee F L b v):=by
  classical
  obtain ⟨gate,sell⟩:=WilsonAddressedMixedStationPages.original (I:=Unit) F simple shop wide quote D target pos
  refine ⟨gate,?_⟩
  intro T δ books ρ d b v f K N p up live L j late before old oldReserve A previous
  have back:f+(K-f)=K:=Nat.add_sub_of_le up.le
  have stored:f+(K-f)≤N:=back.symm ▸ live
  obtain ⟨current,reported,earned⟩:=sell T (fun _=>d) books (fun _=>ρ) (fun _=>b) (fun _=>v)
    f (K-f) N p stored (fun _=>late) (fun _=>before) (fun _=>(before.trans_lt up).trans_le live)
  have sharp:∀x,Arrived R d.val j K N p target (before.trans up.le) live η (current ()) x:=by
    intro x
    simpa only [back] using reported () x
  have ref:=(WilsonReflectedPublicStationFare.original F L (books ρ).checked b v).1
  have eq:=WilsonReflectedMixedIntrinsicAxis.unique R ref (before.trans up.le) live previous sharp
  rw [eq]
  refine ⟨sharp,?_,(earned ()).2,?_⟩
  · simpa only [back] using (earned ()).1
  · intro χ hp
    apply WilsonAddressedPublicGuardFare.cost R hp
    simpa only [back] using (earned ()).1

end YM.Integration.WilsonReflectedMixedSharpAxis
end
