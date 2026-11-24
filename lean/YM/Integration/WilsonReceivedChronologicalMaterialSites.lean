import YM.Integration.WilsonReceivedChronologicalMaterialStream
import YM.Integration.WilsonReceivedChronologicalTwoFlatSale

/-! The physical sites and the independent fixed digits coincide at every age of the posted line. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalMaterialSites
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical
open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology
open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket
open WilsonOlderFreshConnectedBirth WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp
open WilsonOlderFreshConnectedBinding
open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary Stationary
open WilsonOriginalPrimerReceipts WilsonNeutralTwoPrintPathJet
open Primitives.TwoWave AllOrder.Haiku AllOrder.Ink Response PertExtension.Series
open WilsonNeutralTwoPrintPathRoll WilsonOlderFreshConnectedAssembly
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker FVA1Physical FVA1Physical.TwoReset
open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic.Near
open WilsonNeutralTwoPrintPathRead
open WilsonNeutralTwoPrintPathFixed (parcel)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonNeutralTwoPrintPathQuoted (bill)
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Multi
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathDatedPolynomial (row sheet entry)
open WilsonReceivedCoverGrade (Same)
open FundedMarkedPathSelection (output)
open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead WilsonNeutralTwoPrintPeg
open WilsonNeutralTwoPrintPathPolynomial RegulatorIR.Diagram
open WilsonOriginalCensusFaceSites (binder port pin frill root)
open WilsonOriginalCensusDatedSheets (sideValue)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonReceivedCompactVerseEntrance (submit)
open WilsonOriginalCensusFaceSheet (Addressed)
open WilsonReceivedDepositedOrbitalPrint (front)
open WilsonIndependentCollarAddressedSource (Submitted)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonReceivedCoverGrade (Same)
open WilsonOriginalCensusDatedMaterial (words)
open WilsonVacuumPreResetStationaryChange (fine coarse)

open WilsonIndependentCollarMaterialHearing (Mounted)
open WilsonOriginalCensusFaceSchools (Account)
open WilsonOriginalMixedBlockRows (room)
open WilsonReceivedDepositedOrbitalLedger (book)

open WilsonOriginalCensusPublicationClock WilsonOriginalCensusMaterialPosting
open MintClock VowsR



open WilsonReceivedChronologicalMaterialLine (homes)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonReceivedCanonicalSocketGaussian
open WilsonOriginalCensusFaceSites (port)
open WilsonOriginalOccupiedCorridor (sites)
open WilsonReceivedFixedDigitHistory
open OriginalIssuedMarkedRows
open scoped Classical
variable {G:Gauge}{n q m j K per:ℕ}(R:Run G){V:Realm G (q+1) Credit.leanC}
  (draw:V.draws=R.family.path.levels)

abbrev physical (z:Fin n → Site (R.family.side K per)){i:ℕ}(active:i ≤ K):Fin n → Site (R.family.side i per):=
  fun v=>(R.family.S.toDepth active per).parent (z v)

def digits (z:Fin n → Site (R.family.side K per)):Digits R.family.path.levels (Fin n):=fun i v=>
  if active:i+1 ≤ K then (R.family.path.levels.clock.op i per).ratio.residue (physical R z active v) else 0

def footprint (z:Fin n → Site (R.family.side K per))(active:m+1 ≤ K):Fin n → Cover:=
  fun v=>lift (physical R z active v)

private theorem parent (z:Fin n → Site (R.family.side K per))(active:j+1 ≤ K)(v:Fin n):
    (R.family.path.levels.clock.op j per).ratio.parent (physical R z active v)=
      physical R z ((Nat.le_succ j).trans active) v:=by
  exact (Next.Rank.Station.parent_nested _ _ _ (R.family.S.block_odd j)
    (R.family.S.toDepth_odd active per) _).symm

private theorem reverse {A B:Levels G}(same:A=B)(c:Digits B (Fin n)):
    onLevels same (onLevels same.symm c)=c:=by cases same;rfl

include draw in
theorem itinerary (z:Fin n → Site (R.family.side K per))(start:m+1 ≤ K)(a:ℕ)(active:m+a+1 ≤ K)(v:Fin n):
    wrap (R.family.side (m+a+1) per)
      (homes (onLevels draw.symm (digits R z)) (footprint R z start) m a v)=physical R z active v:=by
  induction a with
  | zero => exact wrap_lift _
  | succ a ih =>
    let y:=homes (onLevels draw.symm (digits R z)) (footprint R z start) m a
    let i:=m+a+1
    have bound:i+1 ≤ K:=active
    have step:=WilsonReceivedChronologicalMaterialStream.next (V:=V) (draw:=draw)
      (onLevels draw.symm (digits R z)) (footprint R z start) (m:=m) (j:=m+a) (by omega)
    have fine:=congrArg (fun f:Fin n → Cover=>f v) step
    simp only [Nat.add_sub_cancel_left,show m+a+1-m=a+1 by omega,reverse] at fine
    rw [fine]
    let step:=R.family.path.levels.clock.op i per
    have seated:wrap (R.family.side (i+1) per) (chartIn (loose R.family.path.levels i) y (digits R z i) v)=
        step.ratio.assemble (wrap (R.family.side i per) (y v),digits R z i v):=by
      change wrap (R.family.side (i+1) per) ((loose R.family.path.levels i).L.val • y v+lift (digits R z i v))=
        step.ratio.embed (wrap (R.family.side i per) (y v))+wrap (R.family.side (i+1) per) (lift (digits R z i v))
      rw [map_add,Ratio.embed_wrap]
      rfl
    change wrap (R.family.side (i+1) per) (chartIn (loose R.family.path.levels i) y (digits R z i) v)=physical R z bound v
    rw [seated]
    rw [show wrap (R.family.side i per) (y v)=physical R z ((Nat.le_succ i).trans bound) v from ih ((Nat.le_succ i).trans bound),
      ←parent R z bound, digits, dif_pos bound]
    exact (R.family.path.levels.clock.op i per).ratio.unpack_at _

include draw in
theorem origin (z:Fin n → Site (R.family.side K per))(start:m+1 ≤ K)(a:ℕ)(active:m+a+1 ≤ K):
    (port (R.family.side (m+a+1) per)
      (homes (onLevels draw.symm (digits R z)) (footprint R z start) m a)).origin=physical R z active:=by
  funext v;exact itinerary R draw z start a active v

theorem descended (z:Fin n → Site (R.family.side K per)){c t:ℕ}(past:c ≤ t)(active:t ≤ K):
    sites R (physical R z active) past=physical R z (past.trans active):=by
  refine Nat.decreasingInduction (motive:=fun c h=>sites R (physical R z active) h=physical R z (h.trans active)) ?_ ?_ past
  · intro c younger ih
    rw [show sites R (physical R z active) younger.le=
      (R.family.path.levels.clock.op c per).ratio.parent ∘ sites R (physical R z active) younger from Nat.decreasingInduction_succ_left ..]
    rw [ih]
    funext v
    exact parent R z (Nat.le_trans younger active) v
  · exact Nat.decreasingInduction_self ..

include draw in
theorem resident (z:Fin n → Site (R.family.side K per))(start:m+1 ≤ K)(a c:ℕ)(active:m+a+1+1 ≤ K)
    (past:c ≤ m+a+1)(P:Passport (R.family.side (m+a+1+1) per) (Fin n))
    (registered:P=port _ (homes (onLevels draw.symm (digits R z)) (footprint R z start) m (a+1)))
    (s:Finset (Fin n))(Z:Support (R.family.side c per))
    (arrived:∀v∈s,physical R z (past.trans ((Nat.le_succ _).trans active)) v∈Z):
    ∀v∈s,sites R (P.coarser (R.family.path.levels.clock.op (m+a+1) per).ratio).origin past v∈Z:=by
  have h:P.origin=physical R z active:=registered ▸ origin R draw z start (a+1) active
  have earlier:(P.coarser (R.family.path.levels.clock.op (m+a+1) per).ratio).origin=
      physical R z ((Nat.le_succ _).trans active):=by
    funext v
    change (R.family.path.levels.clock.op (m+a+1) per).ratio.parent (P.origin v)=_
    rw [h,parent]
  rwa [earlier,descended]

end YM.Integration.WilsonReceivedChronologicalMaterialSites
end
