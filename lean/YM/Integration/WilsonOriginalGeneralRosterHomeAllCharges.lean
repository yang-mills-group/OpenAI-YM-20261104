import YM.Integration.WilsonOriginalGeneralRosterHomeInvoices
import YM.Integration.WilsonOriginalGeneralRosterHomeAllSources

/-! The genuine pledged campus pays every occurrence in a mixed finite
household, with a separate positive loss per occurrence. This includes
the weak and the pooled station of each homogeneous or mixed source. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalGeneralRosterHomeAllCharges
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

theorem original {axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}{simple:G.Simple}
    {campaign:Campaign R}{pillars:Campaign.Pillars R campaign}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R campaign pillars)
    (bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h:ℕ)(d:Fin n→Fin (D+1)){δ:ℝ}(books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:Fin n)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    {J:Type}[Fintype J](rows:J→Row (Fin n))(γ:ℝ)(gp:0<γ):
    ∃η:(w:J)→Fin (rows w).size→ℝ,(∀w i,0<η w i) ∧ (∑w,∑i,η w i)<γ ∧
    ∀ᶠr in trail,∀ρ:Fin n→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    ∀(M:Fin n→ℝ)(E:Fin n→ℕ),(∀i,1≤M i)→
    (∀mode:Bool,WilsonReflectedMixedLocatedSchool.Paid F D T d books (fun i s=>field i s mode) M E ρ f)→
    ∀(w:J)(mode branch:Fin (rows w).size→Bool),
    let tag:=(rows w).stock
    let k:=fun i=>(d (tag i)).val
    let book:=fun i=>books (ρ (tag i))
    let L:=fun i=>(book i).rows (d (tag i))
    let v:=fun i=>field (tag i) (ρ (tag i)) (mode i) (branch i)
    let declared:=fun i=>station F (L i) (branch i)
    ∀(N per K req power t:ℕ)(credit:ℝ)(fk:f≤K)(cut:K≤N), f < N →
    ∀panel:Panel R k N per f K fk cut req power t credit,∀file:Filed R k K,
    panel.slot=file.station→panel.axis=file.A N per→(∀i,panel.slot i=declared i)→
    (∀i,panel.names i=((L i).arm (branch i) (v i)).source (N,per))→
      Recruited k panel file (fun i=>cost R (k i) (M (tag i))) (η w) (fun i=>E (tag i)+1) declared:=by
  classical
  obtain ⟨η,ep,total,gate,service,_late⟩:=WilsonOriginalGeneralRosterUnionIncome.original F paid bliss h books d rows γ gp
  refine ⟨η,ep,total,?_⟩
  filter_upwards [WilsonOriginalGeneralRosterHomeAllSources.original F paid bliss slow h d books field gate] with r issued
  intro ρ range root f M E mn campus w mode branch tag k book L v declared N per K req power t credit fk cut below
    panel file slots axes dates names
  have path:=issued ρ range root M E mn campus (rows w).size tag mode branch
  have reached(i:Fin (rows w).size):gate≤panel.slot i:=(path i).1.trans_eq (dates i).symm
  have fitted:=(service w N per f K fk cut req power t credit panel file slots axes reached below).1
  let q:=votes R k (N:=N) (per:=per) file panel.names panel.turn
  obtain ⟨arms,named,restored,sectionAt⟩:=WilsonOriginalGeneralRosterHomeArms.original R k panel file slots axes
  refine ⟨arms,named,restored,?_⟩
  intro e weights radius label phase positive i
  rw [sectionAt i (radius i) (label i) (phase i)]
  have incoming:=fitted i
  change ((C).labels.level (k i)).coeffSize (q i) ≤ WilsonOriginalObservedRoseMeshPurse.quote R k (η w i) (panel.slot i) K N per i (panel.names i) at incoming
  have offer:=quoted R k (panel.slot i) K N per (η w i) i (panel.names i)
  rw [dates i,names i] at incoming offer
  have young:declared i < N:=(dates i) ▸ (panel.before i).trans_lt below
  have trueBill:=(path i).2.2 N per K young fk
  have nonnegative:0≤optical R (k i) (declared i) K (η w i):=mul_nonneg
    (pow_nonneg (div_nonneg (R.family.S.a_pos _).le (R.family.S.a_pos _).le) _) (Real.exp_pos _).le
  exact WilsonOriginalGeneralRosterHomeLedger.deployed R (k i) N per _ K e (E (tag i)+1) cut
    (q i) (cost R (k i) (M (tag i))) (η w i) (weights i)
    (component R (k i) K (radius i) (label i) (phase i)) (positive i)
    (incoming.trans (offer.trans (mul_le_mul_of_nonneg_right trueBill nonnegative)))

end YM.Integration.WilsonOriginalGeneralRosterHomeAllCharges
end
