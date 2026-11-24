import YM.Integration.WilsonIndependentMatchedRosterNativeDose
import YM.Integration.WilsonOriginalPhysicalFruitSchool

/-! The actual admitted physical source, with its selected counterterms,
orientation and translated site, pays the weights of the jointly reported
independent roster before physical regulator removal. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterIssuedDose
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
open MS MS.Land FVA2 FVA2.Register


open WilsonOriginalTwoFlatPublicNamedFare (chosen)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
variable (Jr:ℝ→tower S)(Z:WilsonPrescription G)


open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)

open WilsonReflectedMixedMasterRegistry (Delivery Course)
open WilsonReflectedMixedLocatedSchool (Paid)


open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace

open WilsonIndependentMatchedFiledIncome (plate)
open WilsonOriginalPhysicalFruitVerse (written)
open WilsonOriginalPhysicalFruitDose (amounts)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)

omit [Fintype I] [DecidableEq I] [Nonempty I] in
theorem original (W:Initialize G)(D T h k e u t0:ℕ)(d:I→Fin (D+1))(ex:I→ℕ){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (read:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    (M:I→ℝ)(E:I→ℕ)(C₀:I→Bool→ℝ)(ρ:I→{s:ℝ // 0<s ∧ s<δ})
    (r η roof ceiling:ℝ)(f K power target:ℕ)
    (sale:WilsonReflectedMixedSharpPanel.Purchased F D T h t0 d ex books read M ceiling η power target ρ f K)
    (stamp:WilsonOriginalPhysicalFruitSchool.Stamped F W D T h k e u t0 d ex books read M E C₀ ρ r η roof ceiling f K power target sale):
  ∀N per(live:K ≤ N),
      let axes:=(sale.choose_spec N per live).choose_spec.choose
      ∀(i:I)(mode weak:Bool)(s:Signed)(chi:Bool)(o:Site ((C).side f per)),
      let leg:=(books (ρ i)).rows (d i)
      let j:=station F leg weak
      let Y:=(leg.arm weak (read i (ρ i) mode weak)).source (N,per)
      ∃arm:Arm R (d i).val N per f K,arm.Y=Y ∧ arm.w=(axes i weak).symm (fitted R (d i).val j N per Y) ∧
        arm.b=chi ∧ arm.s=s ∧ arm.o=o ∧
        ∀(t:ℂ)(φ:ℂ →L[ℝ] ℝ)(α:Alma ((C).labels.level (d i).val)→ℝ), (∀v,0≤α v) →
          let slot:=(C).labels.level (d i).val
          let coeffs:=amounts R (d i).val K N per r t (coords R arm)
          WilsonIndependentMatchedFiledIncome.charge e (WilsonOriginalPhysicalFruitVerse.written slot coeffs φ) α ≤
            WilsonIndependentMatchedRosterNativeDose.gross slot e α*‖φ‖*
            (WilsonOriginalPhysicalFruitClock.salary R (d i).val (E i) t (M i) roof *
              ((wilson z r)⁻¹)^WilsonOriginalPhysicalFruitClock.power R (d i).val (E i)*(r/a K)^η):=by
  intro N per live
  dsimp only
  intro i mode weak s chi o
  obtain ⟨arm,hY,hw,hb,hs,ho,pricing⟩:=stamp N per live i mode weak s chi o
  refine ⟨arm,hY,hw,hb,hs,ho,?_⟩
  intro t φ α nonneg
  let slot:=(C).labels.level (d i).val
  let raw:=amounts R (d i).val K N per r t (coords R arm)
  have bill:=WilsonOriginalPhysicalFruitVerse.bought slot raw φ e α nonneg
  have g0:0≤WilsonIndependentMatchedRosterNativeDose.gross slot e α:=
    Finset.sum_nonneg fun v _=>Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>nonneg v
  have b0:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pricing t).1 (norm_nonneg φ)) g0
  exact (bill.trans b0).trans_eq (mul_assoc _ _ _).symm

end YM.Integration.WilsonIndependentMatchedRosterIssuedDose
