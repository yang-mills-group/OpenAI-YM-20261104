import YM.Integration.WilsonReflectedMixedSharpAxis
set_option warningAsError true
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReflectedMixedSharpPanel
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
def Purchased (D T h t:ℕ)(d:I→Fin (D+1))(e:I→ℕ){δ:ℝ}
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
      (∀i b old (η:ℝ) (A:(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val) x,
        Arrived R (d i).val (j i b) K N p old ((first i b).trans up.le) live η A x →
        A.symm x=(axes i b).symm x) ∧
      Gallery F D T h t d books ρ f N p (up.trans_le live)



/-- Per-leg finite reserve. The arity is the largest physical panel, including
any repeated uses of the same registered source. -/
def reserve (n:ℕ)(ζ:ℝ):ℝ:=min (1/32) (ζ/(4*max (1:ℝ) n))

theorem margin (n:ℕ){ζ:ℝ}(pos:0<ζ):0<reserve n ζ ∧ reserve n ζ≤1/32 ∧ (n:ℝ)*reserve n ζ≤ζ/4:=by
  have denom:0<(4:ℝ)*max 1 (n:ℝ):=mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one (le_max_left ..))
  have one:0<reserve n ζ:=lt_min (by norm_num) (div_pos pos denom)
  refine ⟨one,min_le_left ..,?_⟩
  have h:reserve n ζ*(4*max (1:ℝ) n)≤ζ:=(le_div_iff₀ denom).mp (min_le_right ..)
  have h':(n:ℝ)*reserve n ζ ≤ max (1:ℝ) n*reserve n ζ:=mul_le_mul_of_nonneg_right (le_max_right ..) one.le
  linarith

open WilsonReflectedMixedSharedAxis (Pinned)

omit [DecidableEq I] in
/-- For any finite common public roster, the sharper before-period purchase
runs on its actual previously retained axes, at both original report stations. -/
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(wide:∀j,1≤((P).budget j).supportExponent)
    (quote:OPE.Therm.Poetry (P))(D T h target:ℕ){η:ℝ}(pos:0<η)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) →
      (∃i,(ρ i).val=r) →∀(t f K:ℕ)(e:I→ℕ)(field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
      (M:I→ℝ)(cap:ℝ)(power:ℕ),
      Pinned F D T h t d e books field M cap power target ρ f K →
      Purchased F D T h t d e books field M cap η power target ρ f K:=by
  obtain ⟨gate,sale⟩:=WilsonReflectedMixedSharpAxis.original F simple shop wide quote D target pos
  filter_upwards [WilsonAddressedMixedStationRange.original F simple bliss slow D T h gate d books] with r entered
  intro ρ span near t f K e field M cap power fixed
  obtain ⟨up,issued⟩:=fixed
  refine ⟨up,?_⟩
  intro N p live L j
  obtain ⟨first,axes,paid,presold,gallery⟩:=issued N p live
  refine ⟨first,axes,paid,?_,presold,gallery⟩
  intro i b v
  exact sale T books (ρ i) (d i) b v f K N p up live (((entered ρ span near).2 i b).1)
    (first i b) (axes i b) (paid i true b).1

end YM.Integration.WilsonReflectedMixedSharpPanel
end
