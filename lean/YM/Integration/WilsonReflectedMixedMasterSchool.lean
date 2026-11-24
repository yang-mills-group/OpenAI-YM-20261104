import YM.Integration.WilsonReflectedMixedMasterRegistry
import YM.Integration.WilsonReflectedMixedLocatedSchool
set_option warningAsError true
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReflectedMixedMasterSchool
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

def field (D T:ℕ)(d:I→Fin (D+1))(y:∀i,(Spin.comparator (C).book).Field (d i).val)
    (x:∀i,RG17.Free C (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (i:I)(s:{s:ℝ // 0<s ∧ s<δ})(homogeneous b:Bool):S.Field (d i).val:=
  if homogeneous then WilsonPositionHomogeneousFrame.homogeneous F Jr Z s.val (d i).val (x i)
  else chosen F Jr Z s.val ((books s).V (d i)) b (y i) (x i)

/-- Choice of the original fitted matrices at every (slot, source, arm)
before every auxiliary observation of their placed group fields. -/
def Filed (D T h t:ℕ)(d:I→Fin (D+1))(y:∀i,(Spin.comparator (C).book).Field (d i).val)
    (x:∀i,RG17.Free C (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):Prop:=
  let read:=field F Jr Z D T d y x books
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
        Delivery F D T h t d e books read M cap power target ρ f K

omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(wide:∀i,1≤((P).budget i).supportExponent)
    (caps:∀i,((P).budget i).supportExponent≤100)(quote:OPE.Therm.Poetry (P))
    (lead:Leading F Jr)(obedient:∀g:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) g)(D:ℕ):
    ∃t≥D+3,∀(T h:ℕ)(d:I→Fin (D+1))(y:∀i,(Spin.comparator (C).book).Field (d i).val)
    (x:∀i,RG17.Free C (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (_admitted:∀s,WilsonMovingForkWindowBooks.Priced F (books s)),
    Filed F Jr Z D T h t d y x books:=by
  classical
  obtain ⟨t,grade,campus⟩:=WilsonReflectedMixedMasterRegistry.original (I:=I) F simple bliss slow shop wide caps quote D
  refine ⟨t,grade,?_⟩
  intro T h d y x δ books admit
  obtain ⟨Mn,En,npos,entries⟩:=WilsonAddressedMixedNamedIncome.original F Jr Z simple bliss slow lead obedient D T h d y x books
  obtain ⟨Mh,Eh,hpos,columns⟩:=WilsonMovingForkHomeIncome.original F Jr Z simple bliss slow lead obedient D T h d x books admit
  let M(i:I):=max (Mn i) (Mh i)
  let E(i:I):=max (En i) (Eh i)
  have one(i:I):1≤M i:=(npos i).trans (le_max_left ..)
  unfold Filed
  intro read
  refine ⟨M,E,one,?_⟩
  intro e pwr target reserve τ cap power
  have rooms:=campus T h d books read M E one e pwr target reserve
  unfold WilsonReflectedMixedMasterRegistry.Course at rooms
  filter_upwards [rooms,entries,columns] with r opened named homogeneous
  intro ρ span near m f K
  have funded:∀k:Bool,Paid F D T d books (fun i s=>read i s k) M E ρ f:=by
    intro k i b
    have beta:1≤β f:=((P).fits.delayed f).le
    have expand {v w:ℝ}{g:ℕ}(paid:v≤w*(β f)^g)(left:w≤M i)(right:g≤E i):v≤M i*(β f)^(E i):=
      paid.trans (mul_le_mul left (pow_le_pow_right₀ beta right) (pow_nonneg (zero_le_one.trans beta) _) (zero_le_one.trans (one i)))
    cases k with
    | false =>
      have amt:=named ρ span near (fun _=>b) i
      exact ⟨amt.1,expand amt.2.1 (le_max_left ..) (le_max_left ..),expand amt.2.2 (le_max_left ..) (le_max_left ..)⟩
    | true =>
      have amt:=homogeneous ρ span near (fun _=>b) i
      exact ⟨amt.1,expand amt.2.1 (le_max_right ..) (le_max_right ..),expand amt.2.2 (le_max_right ..) (le_max_right ..)⟩
  exact ⟨funded,opened ρ span near fun i k b=>(funded k i b).2.1⟩

omit [DecidableEq I] in
theorem elected (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(wide:∀i,1≤((P).budget i).supportExponent)
    (caps:∀i,((P).budget i).supportExponent≤100)(quote:OPE.Therm.Poetry (P))
    (lead:Leading F Jr)(obedient:∀g:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) g)(D:ℕ):
    ∃t≥D+3,∃T:ℕ,∃δ:ℝ,0<δ ∧ ∃books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val,
    (∀s,WilsonMovingForkWindowBooks.Priced F (books s)) ∧ ∀(h:ℕ)(d:I→Fin (D+1))
    (y:∀i,(Spin.comparator (C).book).Field (d i).val)(x:∀i,RG17.Free C (d i).val),
    Filed F Jr Z D T h t d y x books:=by
  obtain ⟨t,g,cohort⟩:=original (I:=I) F Jr Z simple bliss slow shop wide caps quote lead obedient D
  obtain ⟨T,δ,pos,books,paid⟩:=WilsonMovingForkWindowBooks.original F simple bliss D
  exact ⟨t,g,T,δ,pos,books,paid,fun h d y x=>cohort T h d y x books paid⟩

end YM.Integration.WilsonReflectedMixedMasterSchool
end
