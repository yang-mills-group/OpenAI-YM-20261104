import YM.Integration.WilsonOriginalGeneralRosterHomeCharges
import YM.Integration.WilsonOriginalGeneralRosterUnionIncome

/-! One finite financial purchase covers every occurrence of a pooled
original name, including repeated reflected copies and every proper row.
The houses for source variation are paid once per original stock. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalGeneralRosterHomeLedger
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

theorem deployed (R:Run G)(d N per j K e B:ℕ)(live:K≤N)(q:R.family.label d)(M η:ℝ)
    (weights:Alma (R.family.labels.level d)→ℝ)(phase:ℂ→L[ℝ]ℝ)(nn:∀a,0≤weights a)
    (cash:(R.family.labels.level d).coeffSize q ≤ (M*(R.family.path.levels.clock.hatBeta K)^B)*optical R d j K η):
    WilsonIndependentMatchedFiledIncome.charge e (written (R.family.labels.level d)
      (WilsonOriginalPublicNodalDeployedVote.deployed R d K (N,per) q) phase) weights ≤
    wage R d e weights phase M B j K η:=by
  have value:=WilsonPositionProgramBlockedTrialFiling.price R d N per K live q
  have trueFee:=WilsonOriginalPhysicalFruitVerse.bought _ (entire R d K (N,per) q) phase e weights nn
  apply (WilsonOriginalPublicNodalDeployedVote.original _ R N per K live e _ phase weights nn).trans
  apply mul_le_mul_of_nonneg_left _ (WilsonOriginalPublicNodalDeployedVote.positive _ _)
  apply trueFee.trans
  apply mul_le_mul_of_nonneg_left _ (sum_nonneg fun a _=>sum_nonneg fun j _=>sum_nonneg fun _ _=>nn a)
  exact mul_le_mul_of_nonneg_left (value.trans (mul_le_mul_of_nonneg_left cash (by positivity))) (norm_nonneg _)

theorem original {axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}{simple:G.Simple}
    {campaign:Campaign R}{pillars:Campaign.Pillars R campaign}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R campaign pillars)(bliss:Bliss F l z H)
    (slow:WilsonWindowReportingPace.Slow R.kit)(lead:Leading F Jr)(obeys:∀p,∀ᶠs in trail,Frame.obedient F H (Jr s) p)
    (D T h:ℕ)(d:Fin n→Fin (D+1))(x:∀i,RG17.Free (C) (d i).val){δ:ℝ}
    (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)(window:∀s,WilsonMovingForkWindowBooks.Priced F (books s))
    {J:Type}[Fintype J](rows:J→Row (Fin n))(γ:ℝ)(gp:0<γ):
    ∃η:(w:J)→Fin (rows w).size→ℝ,(∀w i,0<η w i) ∧ (∑w,∑i,η w i)<γ ∧
    ∃(M:Fin n→ℝ)(E:Fin n→ℕ),(∀i,0≤M i) ∧ ∀ᶠr in trail,
    ∀ρ:Fin n→{t:ℝ//0<t ∧ t<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    let L:=fun i=>reading F Jr Z (books (ρ i)) (d i) (x i)
    ∀w:J,let tag:=(rows w).stock; let k:=fun i=>(d (tag i)).val
    ∀(N per f K req power t:ℕ)(credit:ℝ)(fk:f≤K)(cut:K≤N),f < N → reporter F books ρ ≤ K →
    ∀P₀:Panel R k N per f K fk cut req power t credit,∀file:Filed R k K,
    P₀.slot=file.station→P₀.axis=file.A N per→(∀i,P₀.slot i=(L (tag i)).j)→(∀i,P₀.names i=(L (tag i)).arm.source (N,per))→
    let q:=votes R k (N:=N) (per:=per) file P₀.names P₀.turn
    ∀(e:ℕ)(weights:(i:Fin (rows w).size)→Alma ((C).labels.level (k i))→ℝ)(phase:Fin (rows w).size→ℂ→L[ℝ]ℝ),
      (∀i a,0≤weights i a)→∀i,
      WilsonIndependentMatchedFiledIncome.charge e (written ((C).labels.level (k i))
        (WilsonOriginalPublicNodalDeployedVote.deployed R (k i) K (N,per) (q i)) (phase i)) (weights i) ≤
      wage R (k i) e (weights i) (phase i) (M (tag i)) (E (tag i)) (L (tag i)).j K (η w i):=by
  obtain ⟨η,ep,total,gate,funded,_late⟩:=WilsonOriginalGeneralRosterUnionIncome.original F paid bliss h books d rows γ gp
  have high(j:ℕ):((P).budget j).supportExponent≤100:=by rw [paid.support]
  obtain ⟨M,E,nn,earned⟩:=WilsonOriginalObservedRosePooledPurse.original F Jr Z simple bliss slow lead obeys high
    D T h d x books window
  refine ⟨η,ep,total,M,E,nn,?_⟩
  filter_upwards [earned gate] with r earnedHere
  intro ρ range root L w tag k N per f K req power t credit fk cut below enough P₀ file slots axes dates names q e weights phase pos i
  have line:=earnedHere ρ range root
  have reached(a:Fin (rows w).size):gate≤P₀.slot a:=(line (tag a)).1.trans_eq (dates a).symm
  have fitted:=(funded w N per f K fk cut req power t credit P₀ file slots axes reached below).1 i
  change ((C).labels.level (k i)).coeffSize (q i) ≤ WilsonOriginalObservedRoseMeshPurse.quote R k (η w i) (P₀.slot i) K N per i (P₀.names i) at fitted
  have price:=quoted R k (P₀.slot i) K N per (η w i) i (P₀.names i)
  rw [dates i,names i] at fitted price
  have young:(L (tag i)).j < N:=(dates i) ▸ (P₀.before i).trans_lt below
  have rose:variation R k (L (tag i)).j N per i ((L (tag i)).arm.source (N,per))≤M (tag i)*(R.family.path.levels.clock.hatBeta K)^(E (tag i)):=
    (line (tag i)).2.2.2.2 N per K young enough
  have nonnegative:0≤optical R (k i) (L (tag i)).j K (η w i):=mul_nonneg
    (pow_nonneg (div_nonneg (R.family.S.a_pos _).le (R.family.S.a_pos _).le) _) (Real.exp_pos _).le
  exact deployed R (k i) N per _ K e (E (tag i)) cut (q i) (M (tag i)) (η w i) (weights i) (phase i) (pos i)
    (fitted.trans (price.trans (mul_le_mul_of_nonneg_right rose nonnegative)))

end YM.Integration.WilsonOriginalGeneralRosterHomeLedger
end
