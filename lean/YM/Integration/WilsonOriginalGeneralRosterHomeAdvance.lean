import YM.Integration.WilsonOriginalGeneralRosterHomeClinicWages

/-! The entire loss vector is bought from the finite shape once, before
any future optical or thermal price and before the later positive self
tests. Changing a test preserves the exact declared slot in every row. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalGeneralRosterHomeAdvance
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
  {n:ℕ}[Nonempty (Fin n)]
local notation "C" => R.family
local notation "P" => R.family.path.levels


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS
open MS MS.Land FVA2 FVA2.Register


open WilsonOriginalTwoFlatPublicNamedFare (chosen)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
variable (Jr:ℝ→tower S)(Z:WilsonPrescription G)


open WilsonMovingForkSlotDate (slot)
open WilsonMovingForkOpticalBook (reporter)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonOriginalObservedRosePooledWrap (allowance)
open WilsonOriginalObservedRoseMeshHeight (variation)
open Extra.Histories.Motion (orbitCost orbitCost_one_le)

open WilsonOriginalObservedRosePooledPurse (reading)
open WilsonOriginalObservedRoseMeshHeight (tilt)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonReceivedCanonicalVersePortfolio (weight Selection wallet)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOlderFreshSoftSocketMeasuredCash (packet)
open WilsonThermometerPositionTunedSlope (Columns)
open ActualRunPhysicalPages Pert.Asymptotics


open WilsonOriginalPhysicalFruitVerse (written)
open WilsonIndependentMatchedFiledIncome
open WilsonPositionProgramReportedField (entire)
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.StableStrip
open scoped BigOperators

open WilsonOriginalPublicNodalDeployedVote (deployed tariff)
open WilsonOriginalGeneralRosterHomeArms (component)
open WilsonOriginalPhysicalFruitDose (amounts)
open WilsonOriginalPhysicalFruitVerse (written)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)

open WilsonOriginalGeneralRosterHomeCharges (wage optical quoted)
open WilsonOriginalGeneralRosterUnion (Row)

open WilsonMeasuredPublicEntranceGridDebit (fitted)


open WilsonOriginalGeneralRosterHomeInvoices (Recruited)
open WilsonOriginalGeneralRosterHomeAllSources (cost)
open WilsonReflectedPublicStationFare (station)

open WilsonOriginalGeneralRosterHomeClinicCampus (Window)
open WilsonOriginalGeneralRosterHomeMenu (menu)
open XSpace WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Shard WilsonCoeffUV.Soil WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.PathCost
open WilsonPositionProgramTrialHomeFaces

open WilsonOriginalGeneralRosterHomeClinicWages (Offered)
variable {J:Type}[Fintype J]

def carry (main:Row (Fin n))(seed pair:Fin main.size→Test 2)(p:Fin main.size→ℕ)(outside:J→Row (Fin n))
    (η:(w:Unit⊕(Fin main.size⊕J))→Fin (menu main seed p outside w).size→ℝ):
    (w:Unit⊕(Fin main.size⊕J))→Fin (menu main pair p outside w).size→ℝ
  | .inl a=>η (.inl a)
  | .inr (.inl i)=>η (.inr (.inl i))
  | .inr (.inr j)=>η (.inr (.inr j))

omit [Nonempty (Fin n)] in
theorem stays (main:Row (Fin n))(seed pair:Fin main.size→Test 2)(p:Fin main.size→ℕ)(outside:J→Row (Fin n))
    (η:(w:Unit⊕(Fin main.size⊕J))→Fin (menu main seed p outside w).size→ℝ):
    (∑w,∑i,carry main seed pair p outside η w i)=∑w,∑i,η w i:=by
  apply Finset.sum_congr rfl
  rintro (a|j) _
  · rfl
  · cases j <;> rfl

omit [Nonempty (Fin n)] in
theorem shift {D T:ℕ}{δ:ℝ}(d:Fin n→Fin (D+1))(books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:Fin n)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    (main:Row (Fin n))(seed pair:Fin main.size→Test 2)(p:Fin main.size→ℕ)(outside:J→Row (Fin n))
    (η:(w:Unit⊕(Fin main.size⊕J))→Fin (menu main seed p outside w).size→ℝ)(M:Fin n→ℝ)(E:Fin n→ℕ)
    (ρ:Fin n→{s:ℝ//0<s ∧ s<δ})(f:ℕ)
    (issued:Offered F d books field (menu main seed p outside) η M E ρ f):
    Offered F d books field (menu main pair p outside) (carry main seed pair p outside η) M E ρ f:=by
  rintro (a|j)
  · exact issued (.inl a)
  · rcases j with i|v
    · exact issued (.inr (.inl i))
    · exact issued (.inr (.inr v))

theorem original {axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}{simple:G.Simple}
    {campaign:Campaign R}{pillars:Campaign.Pillars R campaign}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R campaign pillars)
    (bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {D T:ℕ}(h:ℕ)(d:Fin n→Fin (D+1)){δ:ℝ}(books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:Fin n)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    (main:Row (Fin n))(seed:Fin main.size→Test 2)(p:Fin main.size→ℕ)(outside:J→Row (Fin n))(γ:ℝ)(gp:0<γ):
    ∃η:(w:Unit⊕(Fin main.size⊕J))→Fin (menu main seed p outside w).size→ℝ,(∀w i,0<η w i) ∧ (∑w,∑i,η w i)<γ ∧
    ∀ᶠr in trail,∀ρ:Fin n→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    ∀(M:Fin n→ℝ)(E:Fin n→ℕ),(∀i,1≤M i)→
    (∀mode:Bool,WilsonReflectedMixedLocatedSchool.Paid F D T d books (fun i s=>field i s mode) M E ρ f)→
    ∀pair:Fin main.size→Test 2,
      (∑w,∑i,carry main seed pair p outside η w i)<γ ∧
      Offered F d books field (menu main pair p outside) (carry main seed pair p outside η) M E ρ f:=by
  obtain ⟨η,ep,total,earned⟩:=WilsonOriginalGeneralRosterHomeAllCharges.original F paid bliss slow D T h d books field
    (menu main seed p outside) γ gp
  refine ⟨η,ep,total,?_⟩
  filter_upwards [earned] with r bought
  intro ρ range root f M E mn school pair
  exact ⟨(stays main seed pair p outside η).trans_lt total,
    shift F d books field main seed pair p outside η M E ρ f (bought ρ range root M E mn school)⟩

end YM.Integration.WilsonOriginalGeneralRosterHomeAdvance
end
