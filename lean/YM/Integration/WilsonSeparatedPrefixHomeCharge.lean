import YM.Integration.WilsonMovingForkHomeIncome
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixHomeCharge
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
      ∀(branch:I→Bool)(χ:I→ℝ), (∀i,0≤χ i) →
      (∀i,let L:=(books (ρ i)).rows (d i)
        let v:=WilsonPositionHomogeneousFrame.homogeneous F Jr Z (ρ i).val (d i).val (x i)
        χ i ≤ max 1 (2*(β f)^(WilsonAddressedMixedStationRange.width T h*((d i).val+1))*
          WilsonReflectedPublicStationFare.fee F L (branch i) v)) →
      ∀(s:Finset I)(P₀:ℕ),(∏i∈s,χ i)*((β f)^(P₀+e))⁻¹≤A*((β f)^P₀)⁻¹:=by
  classical
  obtain ⟨M,E,above,stock⟩:=WilsonMovingForkHomeIncome.original F Jr Z simple bliss slow lead paid D T h d x books window
  let entry (i:I):=WilsonAddressedMixedStationRange.width T h*((d i).val+1)
  let cap:=fun i=>2*M i
  have cOne(i):1≤cap i:=by dsimp [cap];linarith only [above i]
  use ∏i,cap i, Finset.one_le_prod (fun i _=>cOne i), ∑i,(entry i+E i)
  filter_upwards [stock] with r loan ρ band hits m f branch χ nonneg accepted s P₀
  have heat:1≤β f:=((P).fits.delayed f).le
  have positive:0<β f:=zero_lt_one.trans_le heat
  have issued(i):χ i≤cap i*(β f)^(entry i+E i):=by
    have claim:=(loan ρ band hits branch i).2.1
    have base:1≤cap i*(β f)^(entry i+E i):=one_le_mul_of_one_le_of_one_le (cOne i) (one_le_pow₀ heat)
    apply (accepted i).trans (max_le base ?_)
    calc
      _ ≤ (2*(β f)^(entry i))*(M i*(β f)^(E i)):=mul_le_mul_of_nonneg_left claim (by positivity)
      _ = _:=by simp only [cap,pow_add];ring
  have one(i):1≤cap i*(β f)^(entry i+E i):=one_le_mul_of_one_le_of_one_le (cOne i) (one_le_pow₀ heat)
  have subset: (∏i∈s,χ i)≤(∏i,cap i)*(β f)^(∑i,(entry i+E i)):=by
    calc
      _ ≤ ∏i∈s,cap i*(β f)^(entry i+E i):=Finset.prod_le_prod (fun i _=>nonneg i) (fun i _=>issued i)
      _ ≤ ∏i,cap i*(β f)^(entry i+E i):=
        Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ s) (fun i _=>(one i).trans' zero_le_one) (fun i _ _=>one i)
      _ = _:=by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  calc
    _ ≤ ((∏i,cap i)*(β f)^(∑i,(entry i+E i)))*((β f)^(P₀+∑i,(entry i+E i)))⁻¹:=mul_le_mul_of_nonneg_right subset (by positivity)
    _ = _:=by rw [pow_add];field_simp [positive.ne']

end YM.Integration.WilsonSeparatedPrefixHomeCharge
end
