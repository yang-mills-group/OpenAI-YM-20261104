import YM.Integration.WilsonOriginalObservedRoseBornChiralCells
import YM.Integration.WilsonSeparatedPrefixMovingReportedFaculty

/-! The entire preceding binary crossing on the two genuine reflected profiles
of the measured chiral Gram, retaining the signed stable and fitted fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralEars
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

def radius {Q:Fin 2→SealR G}(φ:Wilt Q)(y:ℝ):ℝ:=∑i:Fin 2,|radiusH (φ i) 1 y|

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
        ∀(o:CellR)(c:∀i,Verse (Q i).F)(flag:Fin 2→Bool),
        let Δ:=sector V flag X c φ y o m K N-sector V flag X c φ y o m stop N
        let pay:=2*(terminal flag).buy (epoch V m stop)*(paceT V.draws.S m stop)^2*
          tuition 12 e 12 space⁻¹ (radius φ y) (amount 0 12 primary X c flag) fees
        Auth (ranksV flag 6 (fun i=>(Q i).h)) Δ ∧ Flush e 0 1 Δ pay ∧
        ∀q ≤ e,∀ω:Fin 0→YForest G,‖Δ.2 q 0 ω‖ ≤ pay:=by
  have cap:capP Q=10:=by
    change (∑i:Fin 2,(Q i).h)=10
    rw [Fin.sum_univ_two,six,four]
  obtain ⟨primary,terminal,edges⟩:=WilsonSeparatedPrefixMovingReportedFaculty.original
    (n:=0) M Q v 12 2 height seats (by decide) (by omega) (by omega) (by omega) (by decide)
  obtain ⟨bulb,C,D,φ,fees,hC,hD,source,income,gram⟩:=
    WilsonOriginalObservedRoseBornChiralPurse.original Z a x b R hx ord U prior s small Q y
  obtain ⟨space,book⟩:=income.exists
  refine ⟨bulb,C,D,φ,fees,space,primary,terminal,hC,hD,source,book,gram,?_⟩
  intro V sold X m stop K N matching floor low mid high o c flag
  have radial (i:Fin 2):radiusH (φ i) 1 y ≤ radius φ y:=
    (le_abs_self _).trans (Finset.single_le_sum (fun j _=>abs_nonneg (radiusH (φ j) 1 y)) (Finset.mem_univ i))
  have positive:0<space⁻¹:=inv_pos.mpr (lt_of_lt_of_le zero_lt_one book.pos)
  simpa only [cap, Nat.reduceAdd] using edges V sold X m stop K N matching floor low mid high
    φ fees y (radius φ y) space⁻¹ o positive book.seats radial book.lanes c flag
end YM.Integration.WilsonOriginalObservedRoseBornChiralEars
