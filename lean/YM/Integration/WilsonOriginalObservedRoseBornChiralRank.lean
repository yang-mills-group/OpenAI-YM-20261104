import YM.Integration.WilsonOriginalObservedRoseBornChiralComplete

/-! Keep the native rank of the actual funded R roster in every projected and stable word. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralRank
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


open WilsonIndependentMatchedFittedSeat (receiving)


theorem at_upper (V:Realm G (e+1) J)(X:Courts (H:=H) (v:=v))(m K N:ℕ)(filed:stamp V X m K N)
    (flag:Fin 2→Bool)(φ:Wilt Q)(y:ℝ)(o:CellR):
    sector V flag X (fun i=>dose (X i) 1) φ y o m K N=
      cruises V.draws V.paid N (ranksV flag k (fun s=>(Q s).h)) K m (field flag X φ y o):=by
  apply congrArg (cruises V.draws V.paid N (ranksV flag k (fun s=>(Q s).h)) K m)
  apply congrArg (MassP G ℝ 1)
  funext i
  have low: (X i).m=m:=(filed i).2.2.1
  have top: (X i).m+(X i).i=K:=(filed i).2.2.2.1
  have hi:(X i).i=K-m:=by omega
  exact congrArg (entry (flag i) (X i) 1 (dose (X i) 1) (φ i) y o) hi.symm

theorem fitted (V:Realm G (e+1) J)(X:Courts (H:=H) (v:=v))(m K N:ℕ)
    (filed:stamp V X m K N)(past:m ≤ K)(φ:Wilt Q)(y:ℝ)(o:CellR):
    sector V (choose 1 (quiet 1)) X (fun i=>dose (X i) 1) φ y o m K N=
      stopped V.draws V.paid Q φ (fun i=>home (Q i) (X i)) m K N m y o:=by
  let proj:=fun i=>receiving (X i) 1 (φ i) y o (X i).i
  have lev s: (X s).ax=V.draws:=(filed s).1
  have clock s: (X s).tx=V.paid:=(filed s).2.1
  have bottom s: (X s).m=m:=(filed s).2.2.1
  have top s: (X s).ceilC=K:=(filed s).2.2.2.1
  have prior s: (X s).N=N:=(filed s).2.2.2.2
  have pitch s:paceT (X s).ax.S (X s).m ((X s).m+(X s).i)=paceT V.draws.S m K:=by
    change paceT (X s).ax.S (X s).m (X s).ceilC=_
    rw [lev s,bottom s,top s]
  have born:=WilsonIndependentMatchedAccruedRestart.first V.draws V.paid X φ m K N m y o lev clock bottom top prior
  unfold WilsonIndependentMatchedAccruedRestart.fitted at born
  rw [←cruisesMore _ _ _ le_rfl past] at born
  have fitted: (fun s=>word ((X s).pt-(X s).springP (X s).i) (φ s) (paceT V.draws.S m K) y o (Q s).h)=proj:=by
    funext s
    rw [show proj s=receiving (X s) 1 (φ s) y o (X s).i from rfl,
      WilsonIndependentMatchedFittedSeat.inlet,one_smul,pitch s,(X s).carve1]
    congr 1
    abel
  rw [fitted] at born

  change cruises V.draws V.paid N (capP Q) K m (MassP G ℝ 1 proj)=
    stopped V.draws V.paid Q φ (fun i=>home (Q i) (X i)) m K N m y o at born
  rw [at_upper V X m K N filed,←born]
  simp only [ranksV,WilsonIndependentMatchedRosterMasks.empty,WilsonIndependentMatchedRosterSlots.degree,Bool.false_eq_true,ite_false,capP,asp]
  apply congrArg (cruises V.draws V.paid N _ K m)
  apply congrArg (MassP G ℝ 1)
  funext i
  change entry (choose 1 (quiet 1) i) (X i) 1 (dose (X i) 1) (φ i) y o (X i).i=proj i
  rw [WilsonIndependentMatchedRosterMasks.empty]
  rfl

theorem original (V:Realm G (e+1) J)(X:Courts (H:=H) (v:=v))(m K N:ℕ)
    (filed:stamp V X m K N)(past:m ≤ K)(live:K ≤ N)(φ:Wilt Q)(fees:Fin 2→ℝ)
    (test:∀i,Amplitude (φ i) (fees i))(sound:∀i,On (Q i).h (X i).pt)(y:ℝ)(o:CellR):
    cruises V.draws V.paid N (capP Q) K m (ordinary V.draws X φ m K y o)=
      ∑j:Bits 1,sector V (choose 1 j) X (fun i=>dose (X i) 1) φ y o m K N:=by
  have rows:=WilsonIndependentMatchedPhysicalReturn.exactRows V X φ fees m m K N y o filed le_rfl past live sound test
  rw [←fitted V X m K N filed past φ y o] at rows
  simp_rw [←at_upper V X m K N filed] at rows
  rw [←Finset.sum_erase_add Finset.univ (fun j=>sector V (choose 1 j) X (fun i=>dose (X i) 1) φ y o m K N)
    (Finset.mem_univ (quiet 1))]
  exact (sub_eq_iff_eq_add.mp rows)

end YM.Integration.WilsonOriginalObservedRoseBornChiralRank
