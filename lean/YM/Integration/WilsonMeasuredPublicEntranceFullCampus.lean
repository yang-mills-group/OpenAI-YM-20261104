import YM.Integration.WilsonMeasuredPublicEntranceCutoffFile
import YM.Integration.WilsonReflectedMixedPrescribedSchool
import YM.Integration.WilsonMovingForkHeterogeneousCut
import YM.Integration.WilsonMeasuredPublicEntrancePanelOrder
/-! The physical panel and its measured optical file are funded throughout the closed cutoff interval. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceFullCampus
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

open WilsonMeasuredPublicEntrancePanel (accuracy Panel)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonReflectedMixedSharedAxis (Pinned)
open WilsonReflectedMixedLocatedSchool (Paid)
open WilsonMovingForkHeterogeneousCut (Filed)

/-- Every placement and face has the same genuinely admitted physical names,
station and old finite matrix.  The whole gallery preceding that placement is
used without changing its quiet input or the issued finite source wage. -/
def School (D T t:ℕ)(d:I→Fin (D+1))(e:I→ℕ){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    (M:I→ℝ)(E:I→ℕ)(tuition:ℝ)(power target:ℕ)(ρ:I→{s:ℝ // 0<s ∧ s<δ})(f K:ℕ):Prop:=
  ∃up:f<K,∃electrode:(per:ℕ)→(i:I)→Bool→(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val,
  (∀per i b old (η:ℝ) (A:(C).label (d i).val ≃ₗ[ℂ] (C).label (d i).val) x
    (before:WilsonReflectedPublicStationFare.station F ((books (ρ i)).rows (d i)) b≤K),
    Arrived R (d i).val _ K K per old before le_rfl η A x → A.symm x=(electrode per i b).symm x) ∧
  ∀N per (live:K≤N),
    let L:=fun i=>(books (ρ i)).rows (d i)
    let j:=fun i b=>WilsonReflectedPublicStationFare.station F (L i) b
    ∃ (V:(a:Fin (D+1))→Sight C a.val per)(u:(a:Fin (D+1))→Emblems C a.val)
      (home:∀a:Fin (D+1),Opened C a.val f per),
    (∀a,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N per a.val
      (digits R N per 0) (V a) (u a)) ∧
    ∀n (select:Fin n→I) (mode branch:Fin n→Bool),
      let g:=fun v=>(d (select v)).val
      let Y:=fun v=>((L (select v)).arm (branch v) (field (select v) (ρ (select v)) (mode v) (branch v))).source (N,per)
      ∀(old:Filed R g K),
      let file:=WilsonMeasuredPublicEntranceCutoffFile.complete R g old (fun p v=>electrode p (select v) (branch v))
      file.station=(fun v=>j (select v) (branch v)) →
      ∀requested,(∀v,accuracy g requested v≤e (select v)) →
      ∀(turn:Fin n→Motion)(loc:Fin n→Site ((C).side f per)),
      (∀i k:Fin n,i≠k→((P).budget f).B^2<separation (loc i) (loc k)) →
      ∃A:Panel R g N per f K up.le live requested power t (capital R D tuition),
        A.slot=file.station ∧ A.axis=file.A N per ∧ A.names=Y ∧ A.M=M∘select ∧ A.target=target ∧
        A.tuition=tuition ∧ A.turn=turn ∧ A.loc=loc ∧
        A.sensors=(fun v=>V (d (select v))) ∧ A.stamps=(fun v=>u (d (select v))) ∧
        A.home=(fun v=>home (d (select v))) ∧
        (∀v k,k≤g v→(C).ref k≤N) ∧
        ∀v,Spindle.paid C (g v) f N per (A.names v)≤A.M v*(β f)^(E (select v))

omit [Fintype I] [DecidableEq I] [Nonempty I] in
theorem original {D T h t:ℕ}{d:I→Fin (D+1)}{e:I→ℕ}{δ:ℝ}
    {books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val}
    {field:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    {M:I→ℝ}{E:I→ℕ}{tuition:ℝ}{power target:ℕ}{ρ:I→{s:ℝ // 0<s ∧ s<δ}}{f K:ℕ}
    (one:∀i,1≤M i)
    (salary:∀m:Bool,Paid F D T d books (fun i s=>field i s m) M E ρ f)
    (bought:Pinned F D T h t d e books field M tuition power target ρ f K):
    School F D T t d e books field M E tuition power target ρ f K:=by
  obtain ⟨up,offer⟩:=bought
  let master (N per:ℕ)(valid:K≤N):=(offer N per valid).choose_spec.choose
  refine ⟨up,fun per=>master K per le_rfl,?_,?_⟩
  · intro per i b old η A x before paid
    exact (offer K per le_rfl).choose_spec.choose_spec.2.1 i b old η A x paid
  intro N per live L j
  let first:=(offer N per live).choose
  let axes:=master N per live
  obtain ⟨earned,locked,physical⟩:=(offer N per live).choose_spec.choose_spec
  obtain ⟨V,u,home,enrolled,gallery⟩:=physical
  refine ⟨V,u,home,enrolled,?_⟩
  intro n select mode branch g Y old file stations requested accuracyFits turn loc apart
  have before(v:Fin n):file.station v≤f:=by rw [stations];exact first (select v) (branch v)
  have fixed(v:Fin n):Fixed R (g v) (file.station v) target N per f K (accuracy g requested v) (before v) up.le live
      (Y v) (M (select v)) (tuition*(β K)^power) (file.A N per v):=by
    have axis:file.A N per v=axes (select v) (branch v):=by
      by_cases terminal:N=K
      · subst N
        simp [file,WilsonMeasuredPublicEntranceCutoffFile.complete,axes]
      · have later:K<N:=lt_of_le_of_ne live (Ne.symm terminal)
        have same(x:(C).label (g v)):(file.A N per v).symm x=(axes (select v) (branch v)).symm x:=by
          apply locked (select v) (branch v) file.target (1/32) (file.A N per v) x
          simpa only [stations] using file.arrived N per later v x
        have symmEq:(file.A N per v).symm=(axes (select v) (branch v)).symm:=LinearEquiv.ext same
        simpa using congrArg LinearEquiv.symm symmEq
    rw [axis]
    simp only [stations]
    exact WilsonMeasuredPublicEntrancePanelOrder.lower R (zero_le_one.trans (one _)) (accuracyFits v)
      (earned (select v) (mode v) (branch v))
  let val:=fun v:Fin n=>field (select v) (ρ (select v)) (mode v) (branch v)
  have receipt:=gallery (Fin n) select branch val loc (Stock.census (Fin n)) apart
  let A:Panel R g N per f K up.le live requested power t (capital R D tuition):=
    { slot:=file.station, before:=before, target:=target, tuition:=tuition, M:=M∘select,
      nonneg:=fun v=>zero_le_one.trans (one _), priced:=fun v=>WilsonMeasuredPublicEntrancePanelOrder.placed R D tuition (d (select v)),
      names:=Y, axis:=file.A N per, fixed:=fixed, sensors:=fun v=>V (d (select v)), stamps:=fun v=>u (d (select v)),
      home:=fun v=>home (d (select v)), enrolled:=fun v=>enrolled (d (select v)), turn:=turn, loc:=loc,
      filed:=(receipt.2.1 turn).1 }
  refine ⟨A,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · intro v k support
    exact (home (⟨k,support.trans_lt (d (select v)).isLt⟩:Fin (D+1))).post.trans (up.trans_le live).le
  · intro v
    have paid:=WilsonOriginalTwoFlatPublicFare.issued F (L (select v)) (books (ρ (select v))).checked
      (branch v) (val v) (p:=per) (first (select v) (branch v)) (up.trans_le live)
    exact paid.trans ((salary (mode v) (select v) (branch v)).2.2)

end YM.Integration.WilsonMeasuredPublicEntranceFullCampus
end
