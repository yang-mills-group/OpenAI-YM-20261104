import YM.Integration.WilsonSeparatedPrefixHomeCharge

/-! Restrict the paid master roster after setting its reporter. The original source charges are extended by one on the unused slots. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixSubfaceCharge
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


omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀g:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) g)
    (D T h:ℕ)(d:I→Fin (D+1))
    (x:∀i,RG17.Free C (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃A:ℝ,1≤A ∧ ∃e:ℕ,∀ᶠ r in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},
      (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 m
      ∀(V:Type)(sel:V ↪ I)(branch:V→Bool)(χ:V→ℝ), (∀i,0≤χ i) →
      (∀i,let L:=(books (ρ (sel i))).rows (d (sel i))
        let v:=WilsonPositionHomogeneousFrame.homogeneous F Jr Z (ρ (sel i)).val (d (sel i)).val (x (sel i))
        χ i ≤ max 1 (2*(β f)^(WilsonAddressedMixedStationRange.width T h*((d (sel i)).val+1))*
          WilsonReflectedPublicStationFare.fee F L (branch i) v)) →
      ∀(s:Finset V)(P₀:ℕ),(∏i∈s,χ i)*((β f)^(P₀+e))⁻¹≤A*((β f)^P₀)⁻¹:=by
  classical
  obtain ⟨M,mp,e,all⟩:=WilsonSeparatedPrefixHomeCharge.original F Jr Z simple bliss slow lead paid D T h d x books window
  refine ⟨M,mp,e,?_⟩
  filter_upwards [all] with r sold ρ band hits m f V sel branch χ positive regular s q
  let choice:=Function.extend sel branch (fun _=>false)
  let price:=Function.extend sel χ (fun _=>1)
  have placed(element:V):price (sel element)=χ element:=sel.injective.extend_apply _ _ element
  have turned(element:V):choice (sel element)=branch element:=sel.injective.extend_apply _ _ element
  have vacant (i:I)(no:i∉Set.range sel):price i=1:=by
    exact Function.extend_apply' _ _ i (by simpa only [Set.mem_range] using no)
  have np(i:I):0≤price i:=by
    by_cases entry:i∈Set.range sel
    · obtain ⟨element,rfl⟩:=entry
      simpa only [placed] using positive element
    · rw [vacant i entry];norm_num
  have realprice:=sold ρ band hits choice price np
  have result:=realprice (by
    intro i L v
    by_cases entry:i∈Set.range sel
    · obtain ⟨element,rfl⟩:=entry
      rw [placed,turned]
      exact regular element
    · rw [vacant i entry];exact le_max_left ..) (s.map sel) q
  simpa only [Finset.prod_map,placed] using result

end YM.Integration.WilsonSeparatedPrefixSubfaceCharge
end
