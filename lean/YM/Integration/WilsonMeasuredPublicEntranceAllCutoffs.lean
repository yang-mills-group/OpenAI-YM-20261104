import YM.Integration.WilsonMeasuredPublicEntrancePanelSchool
import YM.Integration.WilsonMeasuredPublicEntranceFullCampus
/-! The same public registration buys all physical charges and the arrived optical panel on both sides of the cutoff boundary. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceAllCutoffs
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

open WilsonReflectedMixedSharedAxis (Pinned)
open WilsonReflectedMixedMasterSchool (field Filed)


open WilsonReflectedMixedPrescribedSchool (Enrolled)
def Registered (D T h t:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (read:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val):Prop:=
  ∃M:I→ℝ,∃E:I→ℕ,(∀i,1≤M i) ∧ ∀(e:I→ℕ)(pwr target:ℕ), (∀i,e i+1≤2*pwr) →
    let τ:=depth ((2*pwr+∑i,E i)+1) (width T h) D
    let cap:=max 1 (4*∑i,M i)
    let power:=(∑i,E i)+WilsonAddressedMixedRawTrial.power T h τ D
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 m
      let K:=berth R τ f
      (∀k:Bool,Paid F D T d books (fun i s=>read i s k) M E ρ f) ∧
        Pinned F D T h t d e books read M cap power target ρ f K ∧
        WilsonMeasuredPublicEntrancePanelCampus.School F D T t d e books read M E cap power target ρ f K ∧
        WilsonMeasuredPublicEntranceFullCampus.School F D T t d e books read M E cap power target ρ f K

omit [DecidableEq I] [Nonempty I] in
theorem original {D T h t:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    {books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val}
    {read:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    (prior:WilsonMeasuredPublicEntrancePanelSchool.Registered F D T h t d books read):Registered F D T h t d books read:=by
  obtain ⟨M,E,one,catalogue⟩:=prior
  refine ⟨M,E,one,?_⟩
  intro e pwr target deep τ cap power
  filter_upwards [catalogue e pwr target deep] with r placed
  intro ρ span near m f K
  obtain ⟨salary,pinned,live⟩:=placed ρ span near
  exact ⟨salary,pinned,live,WilsonMeasuredPublicEntranceFullCampus.original F one salary pinned⟩


end YM.Integration.WilsonMeasuredPublicEntranceAllCutoffs
end
