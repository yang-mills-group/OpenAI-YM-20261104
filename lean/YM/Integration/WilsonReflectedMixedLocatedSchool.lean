import YM.Integration.WilsonReflectedMixedLocatedRegistry
import YM.Integration.WilsonAddressedMixedNamedIncome
import YM.Integration.WilsonMovingForkHomeIncome
set_option warningAsError true
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReflectedMixedLocatedSchool
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
open WilsonReflectedMixedLocatedRegistry (Grant Program)
variable {J:Type}[Fintype J][DecidableEq J]

def Paid (D T:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→S.Field (d i).val)
    (M:I→ℝ)(E:I→ℕ)(ρ:I→{s:ℝ // 0<s ∧ s<δ})(f:ℕ):Prop:=
  ∀i b,let L:=(books (ρ i)).rows (d i)
    let v:=field i (ρ i) b
    let W:=WilsonReflectedPublicStationFare.fee F L b v
    0≤W ∧ W≤M i*(β f)^(E i) ∧ WilsonOriginalTwoFlatPublicFare.charge F L f b v≤M i*(β f)^(E i)

/-- Each cropped reading keeps the two dates of its original finite panel and
the registered fees on both arms. -/
def School (D T h t:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→S.Field (d i).val):Prop:=
  ∃M:I→ℝ,∃E:I→ℕ,(∀i,1≤M i) ∧ ∀(choose:J→I)(e:J→ℕ)(pwr target:ℕ), (∀i,e i+1≤2*pwr) →
  let τ:=depth ((2*pwr+∑i,E i)+1) (width T h) D
  let cap:=max 1 (4*∑i,M i)
  let power:=(∑i,E i)+WilsonAddressedMixedRawTrial.power T h τ D
  ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) →
    (∃i,(ρ i).val=r) →
    let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
    let f:=berth R 5 m
    let K:=berth R τ f
    Paid F D T d books field M E ρ f ∧ Grant F D T t d choose e books field M cap power target ρ f K

omit [DecidableEq I] in
private theorem appointed (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(wide:∀i,1≤((P).budget i).supportExponent)
    (caps:∀i,((P).budget i).supportExponent≤100)(quote:OPE.Therm.Poetry (P))(D:ℕ):
    ∃t≥D+3,∀(T h:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→S.Field (d i).val)
    (M:I→ℝ)(E:I→ℕ)(_one:∀i,1≤M i),
    (∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      Paid F D T d books field M E ρ (berth R 5 m)) →
    School (J:=J) F D T h t d books field:=by
  classical
  obtain ⟨t,grade,issued⟩:=WilsonReflectedMixedLocatedRegistry.original (I:=I) (J:=J) F simple bliss slow shop wide caps quote D
  refine ⟨t,grade,?_⟩
  intro T h d δ books field M E one salary
  refine ⟨M,E,one,?_⟩
  intro choose e pwr target reserve τ cap power
  have bill:=issued T h d choose e books field M E one pwr target reserve
  unfold Program at bill
  filter_upwards [bill,salary] with r registered presold
  intro ρ span near m f K
  have paid:=presold ρ span near
  exact ⟨paid,registered ρ span near fun i b=>(paid i b).2.1⟩

omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(wide:∀i,1≤((P).budget i).supportExponent)
    (caps:∀i,((P).budget i).supportExponent≤100)(quote:OPE.Therm.Poetry (P))
    (lead:Leading F Jr)(obedient:∀g:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) g)(D:ℕ):
    ∃t≥D+3,∀(T h:ℕ)(d:I→Fin (D+1))(y:∀i,(Spin.comparator R.family.book).Field (d i).val)
    (x:∀i,RG17.Free C (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val),
    School (J:=J) F D T h t d books
      (fun i s b=>chosen F Jr Z s.val ((books s).V (d i)) b (y i) (x i)) ∧
    ((∀s,WilsonMovingForkWindowBooks.Priced F (books s)) → School (J:=J) F D T h t d books
      (fun i s _=>WilsonPositionHomogeneousFrame.homogeneous F Jr Z s.val (d i).val (x i))):=by
  classical
  obtain ⟨t,grade,market⟩:=appointed (I:=I) (J:=J) F simple bliss slow shop wide caps quote D
  refine ⟨t,grade,?_⟩
  intro T h d y x δ books
  obtain ⟨M,E,one,fare⟩:=WilsonAddressedMixedNamedIncome.original F Jr Z simple bliss slow lead obedient D T h d y x books
  constructor
  · apply market T h d books _ M E one
    filter_upwards [fare] with r priced
    intro ρ span near m i b
    exact priced ρ span near (fun _=>b) i
  · intro window
    obtain ⟨M',E',one',fare'⟩:=WilsonMovingForkHomeIncome.original F Jr Z simple bliss slow lead obedient D T h d x books window
    apply market T h d books _ M' E' one'
    filter_upwards [fare'] with r priced
    intro ρ span near m i b
    exact priced ρ span near (fun _=>b) i

end YM.Integration.WilsonReflectedMixedLocatedSchool
end
