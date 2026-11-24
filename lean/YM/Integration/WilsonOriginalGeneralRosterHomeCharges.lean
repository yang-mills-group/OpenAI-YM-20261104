import YM.Integration.WilsonOriginalGeneralRosterFiledIncome
import YM.Integration.WilsonOriginalGeneralRosterHomeArms
import YM.Integration.WilsonOlderFreshSoftSocketCohortCash

/-! The independently chosen losses buy the actual home-scaled coefficient
charges uniformly in the original cutoff and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterHomeCharges
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

def optical (R:Run G)(d j K:ℕ)(η:ℝ):ℝ:=
  (R.family.S.a j/R.family.S.a K)^d*Real.exp (η*(R.family.S.scale K-R.family.S.scale j))

def wage (R:Run G)(d e:ℕ)(A:Alma (R.family.labels.level d)→ℝ)(p:ℂ→L[ℝ]ℝ)
    (M:ℝ)(h j K:ℕ)(η:ℝ):ℝ:=
  let B:=R.family.labels.level d
  tariff B (R.family.path.levels.clock.hatBeta K)*
    ((∑i:Alma B,∑t∈range (e+1),∑_∈Finset.HasAntidiagonal.antidiagonal t,A i)*
      (‖p‖*(2^(univ.sup (fun i:B.Index=>(B.grades i).2))*
        ((M*(R.family.path.levels.clock.hatBeta K)^h)*optical R d j K η))))

omit [Nonempty (Fin n)] in
theorem quoted (R:Run G)(k:Fin n→ℕ)(j K N per:ℕ)(η:ℝ)(i:Fin n)(Y:R.family.label (k i)):
    WilsonOriginalObservedRoseMeshPurse.quote R k η j K N per i Y ≤ variation R k j N per i Y*optical R (k i) j K η:=by
  let b:=2*orbitCost (R.family.labels.level (k i))*((1+WilsonOriginalMicroscopicGuardedPage.wrapCost R (k i) j)*
    Next.Rank.Spindle.paid R.family (k i) j N per Y)
  have shift:0≤optical R (k i) j K η:=mul_nonneg
    (pow_nonneg (div_nonneg (R.family.S.a_pos _).le (R.family.S.a_pos _).le) _) (Real.exp_pos _).le
  calc
    _=b*optical R (k i) j K η:=by
      unfold b optical WilsonOriginalObservedRoseMeshPurse.quote WilsonOriginalMicroscopicGuardedReporters.stretch
      ring
    _ ≤ |b| * optical R (k i) j K η:=mul_le_mul_of_nonneg_right (le_abs_self b) shift
    _=_:=rfl

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(lo:∀j,1≤((P).budget j).supportExponent)
    (lead:Leading F Jr)(paid:∀g:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) g)
    (hi:∀j,((P).budget j).supportExponent≤100)(D T h:ℕ)(d:Fin n→Fin (D+1))
    (x:∀i,RG17.Free (C) (d i).val){δ:ℝ}(books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s))(γ:ℝ)(gp:0<γ):
    let k:=fun i=>(d i).val
    ∃η:Fin n→ℝ,(∀i,0<η i) ∧ (∑i,η i)<γ ∧ ∃(M:Fin n→ℝ)(E:Fin n→ℕ),(∀i,0≤M i) ∧
    ∀ᶠr in trail,∀ρ:Fin n→{t:ℝ//0<t ∧ t<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    let L:=fun i=>reading F Jr Z (books (ρ i)) (d i) (x i)
    ∀(N per f K req power tag:ℕ)(credit:ℝ)(fk:f≤K)(cut:K≤N),f < N → reporter F books ρ ≤ K → 
    ∀P₀:Panel R k N per f K fk cut req power tag credit,∀file:Filed R k K,
    P₀.slot=file.station→P₀.axis=file.A N per→(∀i,P₀.slot i=(L i).j)→(∀i,P₀.names i=(L i).arm.source (N,per))→
    let q:=votes R k (N:=N) (per:=per) file P₀.names P₀.turn
    ∀(e:ℕ)(A:(i:Fin n)→Alma ((C).labels.level (k i))→ℝ)(p:Fin n→ℂ→L[ℝ]ℝ),(∀i a,0≤A i a)→
    ∀i,WilsonIndependentMatchedFiledIncome.charge e (written ((C).labels.level (k i)) (deployed R (k i) K (N,per) (q i)) (p i)) (A i)≤
      wage R (k i) e (A i) (p i) (M i) (E i) (L i).j K (η i):=by
  intro k
  obtain ⟨η,ep,total,gate,fit⟩:=WilsonOriginalGeneralRosterFiledIncome.original R k simple shop lo γ gp
  obtain ⟨M,E,nn,raw⟩:=WilsonOriginalObservedRosePooledPurse.original F Jr Z simple bliss slow lead paid hi D T h d x books window
  refine ⟨η,ep,total,M,E,nn,?_⟩
  filter_upwards [raw gate] with r covered
  intro ρ span near L N per f K req power tag credit fk cut deep top P₀ file stations axes dates names q e A p nonneg i
  have panel:=covered ρ span near
  have reached(i:Fin n):gate≤P₀.slot i:=(panel i).1.trans_eq (dates i).symm
  have bought:=(fit N per f K fk cut req power tag credit P₀ file stations axes reached deep).1 i
  have upper:=quoted R k (P₀.slot i) K N per (η i) i (P₀.names i)
  change ((C).labels.level (k i)).coeffSize (q i) ≤ WilsonOriginalObservedRoseMeshPurse.quote R k (η i) (P₀.slot i) K N per i (P₀.names i) at bought
  rw [dates i,names i] at bought upper
  have opt:0≤optical R (k i) (L i).j K (η i):=mul_nonneg
    (pow_nonneg (div_nonneg (R.family.S.a_pos _).le (R.family.S.a_pos _).le) _) (Real.exp_pos _).le
  have young:(L i).j < N:=(dates i) ▸ (P₀.before i).trans_lt deep
  have bill:=bought.trans (upper.trans
    (mul_le_mul_of_nonneg_right ((panel i).2.2.2.2 N per K young top) opt))
  have value:=WilsonPositionProgramBlockedTrialFiling.price R (k i) N per K cut (q i)
  have rawPrice:=WilsonOriginalPhysicalFruitVerse.bought _ (entire R (k i) K (N,per) (q i)) (p i) e (A i) (nonneg i)
  apply (WilsonOriginalPublicNodalDeployedVote.original _ R N per K cut e _ (p i) (A i) (nonneg i)).trans
  apply mul_le_mul_of_nonneg_left _ (WilsonOriginalPublicNodalDeployedVote.positive _ _)
  apply rawPrice.trans
  apply mul_le_mul_of_nonneg_left _ (sum_nonneg fun a _=>sum_nonneg fun q _=>sum_nonneg fun _ _=>nonneg i a)
  exact mul_le_mul_of_nonneg_left (value.trans (mul_le_mul_of_nonneg_left bill (by positivity))) (norm_nonneg _)

end YM.Integration.WilsonOriginalGeneralRosterHomeCharges
end
