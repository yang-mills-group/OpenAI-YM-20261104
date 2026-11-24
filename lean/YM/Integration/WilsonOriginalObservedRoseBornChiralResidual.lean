import YM.Integration.WilsonOriginalObservedRoseBornChiralEars
import YM.Integration.WilsonIndependentMatchedPhysicalReturn

/-! On the original reported vacuum, the entire charged stationary minus
evolved fitted pair has precisely its three signed stable contributions.
Every first binary crossing is paid at moment twelve on the bought bulb. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralResidual
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
variable {G:Gauge}{e u₀:ℕ}{H:Hol G}
local notation "J" => Credit.leanC


open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonOriginalObservedRoseBornChiralEars (radius)
open WilsonIndependentMatchedRosterMasks (Bits choose quiet)
open WilsonIndependentMatchedPhysicalReturn (ordinary)
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentMatchedPhysicalSector (field)
open private summed from YM.Integration.WilsonIndependentMatchedRosterPlanted

variable {Q:Fin 2→SealR G}{v:∀i,Rails (Q i).h 6 u₀ e}

def issued (V:Realm G (e+1) J) (φ:Wilt Q)(X:Courts (H:=H) (v:=v))
    (y:ℝ)(o:CellR)(m stop K N:ℕ):Era G ℝ:=
  (cruises V.draws V.paid N (capP Q) K m (ordinary V.draws X φ m K y o)-
    stopped V.draws V.paid Q φ (fun i=>home (Q i) (X i)) m K N m y o)-
    ∑j∈Finset.univ.erase (quiet 1),sector V (choose 1 j) X (fun i=>dose (X i) 1) φ y o m stop N

theorem at_upper (V:Realm G (e+1) J)(X:Courts (H:=H) (v:=v))(m K N:ℕ)(filed:stamp V X m K N)
    (flag:Fin 2→Bool)(φ:Wilt Q)(y:ℝ)(o:CellR):
    sector V flag X (fun i=>dose (X i) 1) φ y o m K N=
      cruises V.draws V.paid N (ranksV flag 6 (fun s=>(Q s).h)) K m (field flag X φ y o):=by
  apply congrArg (cruises V.draws V.paid N (ranksV flag 6 (fun s=>(Q s).h)) K m)
  apply congrArg (MassP G ℝ 1)
  funext i
  have low: (X i).m=m:=(filed i).2.2.1
  have top: (X i).m+(X i).i=K:=(filed i).2.2.2.1
  have hi:(X i).i=K-m:=by omega
  exact congrArg (entry (flag i) (X i) 1 (dose (X i) 1) (φ i) y o) hi.symm

theorem signed (V:Realm G (e+1) J)(X:Courts (H:=H) (v:=v))(m stop K N:ℕ)
    (filed:stamp V X m K N)(past:m ≤ K)(live:K ≤ N)
    (φ:Wilt Q)(fees:Fin 2→ℝ)(test:∀i,Amplitude (φ i) (fees i))
    (sound:∀i,On (Q i).h (X i).pt)(y:ℝ)(o:CellR):
    issued V φ X y o m stop K N=
      ∑j∈Finset.univ.erase (quiet 1),(sector V (choose 1 j) X (fun i=>dose (X i) 1) φ y o m K N-
        sector V (choose 1 j) X (fun i=>dose (X i) 1) φ y o m stop N):=by
  have rows:=WilsonIndependentMatchedPhysicalReturn.exactRows V X φ fees m m K N y o filed le_rfl past live sound test
  unfold issued
  rw [rows,Finset.sum_sub_distrib]
  simp only [at_upper V X m K N filed]

theorem original (M:Master H)(Q:Fin 2→SealR G)(six:(Q 0).h=6)(four:(Q 1).h=4)
    (v:∀i,Rails (Q i).h 6 u₀ e)(height seats:ℕ)(room:12 ≤ seats)(width:12 ≤ u₀)
    (Z:WilsonPrescription G)(a:Axis)(x:E4)(hx:0<x a){I:Type}[Fintype I](b:I→Sec G 6)
    (R:Run G)(ord:Extraction.Order)(U:Filter (ℕ×ℕ))(prior:U ≤ ord.fuse)
    (s:ℝ→ℕ)(small:Tendsto (aperture R s) trail (𝓝 0))(y:ℝ):
    ∃bulb:Bulb (site x) a,∃C:ℝ,∃D:I→ℝ,∃φ:Wilt Q,∃fees:Fin 2→ℝ,∃space:ℝ,
    ∃primary:Fin 2→Credit,∃terminal:(Fin 2→Bool)→Credit,
      0<C ∧ (∀i,0 ≤ D i) ∧ (∀i,(φ i).ψ.val=shape a x bulb i) ∧ Bough Q φ y space fees ∧
      (∀ᶠ t:ℝ×(ℕ×ℕ) in trail.curry U,
        let board₀:=board R (s t.1) t.1 t.2.2
        Z.store.Meets Z.scheme board₀ 6 ∧ Paid Z a x b bulb C D board₀) ∧
      ∀(V:Realm G (e+1) J)(_sold:Elected M V height seats)(X:Courts (H:=H) (v:=v))
        (m stop K N:ℕ),stamp V X m K N → V.anchor ≤ m → m ≤ stop → stop ≤ K → K ≤ N →
        (∀i,On (Q i).h (X i).pt) → ∀(o:CellR),
        let wage:=∑j∈Finset.univ.erase (quiet 1),
          let flag:=choose 1 j
          2*(terminal flag).buy (epoch V m stop)*(paceT V.draws.S m stop)^2*
            tuition 12 e 12 space⁻¹ (radius φ y) (amount 0 12 primary X (fun i=>dose (X i) 1) flag) fees
        response e 0 (issued V φ X y o m stop K N) wage:=by
  obtain ⟨bulb,C,D,φ,fees,space,primary,terminal,hC,hD,source,book,matrix,edges⟩:=
    WilsonOriginalObservedRoseBornChiralEars.original M Q six four v height seats room width
      Z a x hx b R ord U prior s small y
  refine ⟨bulb,C,D,φ,fees,space,primary,terminal,hC,hD,source,book,matrix,?_⟩
  intro V sold X m stop K N filed floor lo mid hi sound o wage
  rw [signed V X m stop K N filed (lo.trans mid) hi φ fees book.lanes sound y o]
  apply summed
  intro j _
  exact (edges V sold X m stop K N filed floor lo mid hi o (fun i=>dose (X i) 1) (choose 1 j)).2

end YM.Integration.WilsonOriginalObservedRoseBornChiralResidual
