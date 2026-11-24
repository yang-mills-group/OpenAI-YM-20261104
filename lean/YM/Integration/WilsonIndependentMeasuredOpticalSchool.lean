import YM.Integration.WilsonMeasuredPublicEntranceAllCutoffs
import YM.Integration.WilsonIndependentMeasuredOpticalFiling

/-! The same physical grant that elects every measured direction pays its
whole fitted face on the independently matched optical epoch. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
namespace YM.Integration.WilsonIndependentMeasuredOpticalSchool
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
open WilsonPositionProgramTrialOpticalBand (Band)
open WilsonIndependentMeasuredOpticalWindow (Slot)
open WilsonIndependentMeasuredOpticalFiling (AllFaces)

omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {axis:Axis}{ε:ℝ}(course:WilsonPositionProgramArithmetic.course simple axis ε R.kit)
    {d₀:ℕ}(hd:0<d₀)(ratio:Z.run.ratio=(3:ℕ)^d₀)(stage:ℕ)
    {D T h t:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    {books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val}
    {read:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    (prior:WilsonMeasuredPublicEntrancePanelSchool.Registered F D T h t d books read) :
    ∃M:I→ℝ,∃E:I→ℕ,(∀i,1  ≤  M i) ∧ ∀(e:I→ℕ)(pwr target:ℕ),(∀i,e i+1  ≤  2*pwr) →
      let τ:=depth ((2*pwr+∑i,E i)+1) (width T h) D
      let cap:=max 1 (4*∑i,M i)
      let power:=(∑i,E i)+WilsonAddressedMixedRawTrial.power T h τ D
      ∃B:Band R Z.run (berth R τ) stage,∀seats q:ℕ,∀ᶠr in trail,
        ∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r  ≤  (ρ i).val ∧ (ρ i).val  ≤  outer z h r) → (∃i,(ρ i).val=r) →
        let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
        let f:=berth R 5 m
        let K:=berth R τ f
        let i:=B.mesh (f-B.reporter)
        Pinned F D T h t d e books read M cap power target ρ f K ∧
          WilsonMeasuredPublicEntranceFullCampus.School F D T t d e books read M E cap power target ρ f K ∧
          (∀b:Bool,Paid F D T d books (fun v s=>read v s b) M E ρ f) ∧
          B.reporter  ≤  f ∧ 0 < i ∧ a f  ≤  r ∧ Slot R Z.run f K i ∧
          (∀v,(ρ v).val/a f  ≤  (Z.run.den i:ℝ)^(2*T+11+2*h)) ∧
          AllFaces R Z.run f K i seats power q (WilsonMeasuredPublicEntrancePanelOrder.capital R D cap) := by
  obtain ⟨M,E,one,school⟩:=WilsonMeasuredPublicEntranceAllCutoffs.original F prior
  refine ⟨M,E,one,?_⟩
  intro e pwr target deep τ cap power
  have long:2  ≤  τ := by dsimp [τ,depth];omega
  obtain ⟨B,cash⟩:=WilsonIndependentMeasuredOpticalWindow.original F simple bliss slow Z.run course hd ratio stage τ long D T h d books
  refine ⟨B,?_⟩
  intro seats q
  filter_upwards [school e pwr target deep,cash (8*(power*seats+q)+1)] with r physical matched
  intro ρ spread near m f K i
  obtain ⟨earned,pin,_,all⟩:=physical ρ spread near
  obtain ⟨placed,room,tiny,board,homes⟩:=matched ρ spread near
  change 8*(power*seats+q)+1 ≤ i at room
  refine ⟨pin,all,earned,placed,by omega,tiny,board,homes,?_⟩
  have enough:8*(power*seats+q) ≤ i := (Nat.le_succ _).trans room
  exact WilsonIndependentMeasuredOpticalFiling.original R Z.run simple board enough
    (WilsonMeasuredPublicEntrancePanelOrder.capital R D cap) (le_max_left ..)

end YM.Integration.WilsonIndependentMeasuredOpticalSchool
