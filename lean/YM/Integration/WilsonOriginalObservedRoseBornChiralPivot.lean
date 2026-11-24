import YM.Integration.WilsonOriginalObservedRoseBornChiralFirstRate

/-! The two reflected ears in their native detector-then-upper order, using any already elected compact bulb. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralPivot
open YM.WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonIndependentMatchedRosterLane WilsonIndependentMatchedCoverPairBudget
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedRosterSlots (entry wallet degree count)
open WilsonIndependentMatchedPhysicalComponent (volume price)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentMatchedPhysicalMasks (ranksV)
open WilsonSeparatedPrefixMovingReportedLanes (Courts row amount)
open WilsonSeparatedPrefixMovingReportedStableEdge (tuition)
open WilsonSeparatedPrefixMovingReportedStableLaw (reading)
open WilsonIndependentMatchedPhysicalSector (stamp)
open WilsonIndependentMovingRosterAllFineSeats (Elected)
open WilsonSeparatedPrefixMovingCalendar (epoch)

open WilsonSeparatedPrefixMovingReportedFaculty (sector)
open Trace Trace.Pilot FVA2 FVA2.Register Spec Extraction OPE PhysicalNext.Repeat.Legato
open Maxwell Maxwell.Free XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Photo
open WilsonMaxwellThermometerReflectedIncidence Table.Pairing
open WilsonMaxwellThermometerPublicStation (aperture)
open WilsonMaxwellThermometerSignedWallet (board)
open WilsonPhysicalChiralPairReading (Paid)
open WilsonPositionProgramReflectedPurse (shape)
open MS MS.WilsonBridge.Coupling
variable {G:Gauge}{k e u₀:ℕ}{H:Hol G}
local notation "J" => Credit.leanC


open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonOriginalObservedRoseBornChiralEars (radius)
open WilsonIndependentMatchedRosterMasks (Bits choose quiet)
open WilsonIndependentMatchedPhysicalReturn (ordinary)
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentMatchedPhysicalSector (field)
open private summed from YM.Integration.WilsonIndependentMatchedRosterPlanted

variable {Q:Fin 2→SealR G}{v:∀i,Rails (Q i).h k u₀ e}

open WilsonOriginalObservedRoseBornChiralRankHome (bill)
open WilsonOriginalObservedRoseBornChiralRankOffice (wage)

open WilsonOriginalObservedRoseBornChiralProper (submitted atGrade stableFee fittedFee)
open WilsonOriginalObservedRoseBornChiralProducts (centered)
open WilsonIndependentMatchedFittedSeat (receiving)

open WilsonOriginalObservedRoseBornChiralHearing (first projected)
open WilsonOriginalObservedRoseBornChiralDelta (portfolio)
open WilsonIndependentMatchedRosterLane (chargeBelow)

/-- The reporting vector uniquely determines the fitted finite word at every date on its one school. -/
theorem single {Q:SealR G}{v:Rails Q.h k u₀ e}(X Y:CutsP H Q.ans Q.path v J J J J)
    (school:X.L=Y.L)(older:X.m=Y.m)(length:X.i=Y.i)(top:X.N=Y.N)(vote:home Q X=home Q Y)
    (φ:Rarity Q.D)(y:ℝ)(o:CellR):
    receiving X 1 φ y o=receiving Y 1 φ y o:=by
  have ax:X.ax=Y.ax:=congrArg (fun l=>l.L.V.draws) school
  have tx:X.tx=Y.tx:=congrArg (fun l=>l.L.V.paid) school
  have K:X.ceilC=Y.ceilC:=congrArg₂ (·+·) older length
  have tiles:X.tileP=Y.tileP:=by
    rw [←(WilsonPositionProgramTrialAccrued.returns Q X).1,←(WilsonPositionProgramTrialAccrued.returns Q Y).1]
    rw [ax,tx,older,K,top,vote]
  have doses:dose X 1=dose Y 1:=by
    unfold dose WilsonIndependentMatchedReportedProxy.reported
    rw [ax,tx,top,older,length,tiles]
  have same:X.vesselsC=Y.vesselsC:=congrArg (fun l=>l.L.V) school
  unfold receiving
  rw [same,older,top]
  exact congrArg (fun c:Verse Q.F=>WilsonIndependentMatchedCoveredSeats.printed Y.vesselsC
    (WilsonIndependentMatchedReportedProxy.sectionSeal Q.ans Q.path) φ c Y.m Y.N y o) doses

theorem original (V:Realm G (e+1) J)(X Y:Courts (H:=H) (v:=v))(φ:Wilt Q)(m K N:ℕ)
    (filed:stamp V X m K N)(registered:stamp V Y m K N)(school:∀i,(X i).L=(Y i).L)
    (votes:∀i,home (Q i) (X i)=home (Q i) (Y i))(y:ℝ)(o:CellR)(ω:Fin 0→YForest G):
    projected V X φ m K N y o ω=projected V Y φ m K N y o ω:=by
  have same (i:Fin 2):receiving (X i) 1 (φ i) y o=receiving (Y i) 1 (φ i) y o:=by
    obtain ⟨_,_,old₀,cut₀,N₀⟩:=filed i
    obtain ⟨_,_,old₁,cut₁,N₁⟩:=registered i
    have marks:(X i).i=(Y i).i:=by
      change (X i).m+(X i).i=K at cut₀
      change (Y i).m+(Y i).i=K at cut₁
      omega
    exact single (X i) (Y i) (school i) (old₀.trans old₁.symm) marks (N₀.trans N₁.symm) (votes i) (φ i) y o
  unfold projected
  rw [funext votes,same 0,same 1]

end YM.Integration.WilsonOriginalObservedRoseBornChiralPivot
